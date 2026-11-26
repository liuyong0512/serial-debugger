# -*- coding: utf-8 -*-
"""串口调试助手（Python / tkinter / pyserial）"""

import codecs
import datetime
import queue
import re
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, filedialog

try:
    import serial
    from serial.tools import list_ports
except ImportError:
    messagebox.showerror("缺少依赖", "请先安装 pyserial：\npython -m pip install pyserial")
    raise SystemExit(1)


BAUD_CANDIDATES = [9600, 19200, 38400, 57600, 74880, 115200,
                   230400, 460800, 921600, 4800, 2400]
COMMON_BAUDS = ["2400", "4800", "9600", "19200", "38400", "57600",
                "74880", "115200", "230400", "460800", "921600"]
PARITY_MAP = {
    "无 (None)": serial.PARITY_NONE,
    "偶 (Even)": serial.PARITY_EVEN,
    "奇 (Odd)": serial.PARITY_ODD,
}
STOP_MAP = {"1": serial.STOPBITS_ONE, "2": serial.STOPBITS_TWO}
EOL_MAP = {"无": "", "CR+LF": "\r\n", "LF": "\n", "CR": "\r"}
ENCODINGS = ["utf-8", "gbk", "gb18030", "iso-8859-1", "ascii", "big5"]


def now_stamp():
    return datetime.datetime.now().strftime("%H:%M:%S.%f")[:-3]


def file_stamp():
    return datetime.datetime.now().strftime("%Y%m%d-%H%M%S")


def format_hex(data, with_offset):
    lines = []
    for i in range(0, len(data), 16):
        chunk = data[i:i + 16]
        hex_part = " ".join("%02X" % b for b in chunk)
        ascii_part = "".join(chr(b) if 32 <= b <= 126 else "." for b in chunk)
        prefix = "%08X  " % i if with_offset else ""
        lines.append(prefix + hex_part.ljust(47) + "  |" + ascii_part + "|")
    return "\n".join(lines) + ("\n" if lines else "")


def parse_hex(text):
    clean = re.sub(r"0x", "", text, flags=re.IGNORECASE)
    clean = re.sub(r"[\s,;:\-\n\r\t]", "", clean)
    if not clean:
        return b""
    if not re.fullmatch(r"[0-9a-fA-F]+", clean):
        raise ValueError("HEX 内容包含非法字符")
    if len(clean) % 2:
        raise ValueError("HEX 字符数必须为偶数")
    return bytes.fromhex(clean)


def parse_escapes(text):
    out = bytearray()
    buf = ""

    def flush():
        nonlocal buf
        if buf:
            out.extend(buf.encode("utf-8", errors="replace"))
            buf = ""

    i = 0
    while i < len(text):
        ch = text[i]
        if ch != "\\":
            buf += ch
            i += 1
            continue
        if i + 1 >= len(text):
            buf += "\\"
            break
        nxt = text[i + 1]
        if nxt in ("r", "n", "t"):
            flush()
            out.append({"r": 13, "n": 10, "t": 9}[nxt])
            i += 2
        elif nxt == "x" and i + 3 < len(text) and re.fullmatch(r"[0-9a-fA-F]{2}", text[i + 2:i + 4]):
            flush()
            out.append(int(text[i + 2:i + 4], 16))
            i += 4
        elif nxt == "\\":
            flush()
            out.append(92)
            i += 2
        else:
            buf += "\\" + nxt
            i += 2
    flush()
    return bytes(out)


def score_data(data, errors):
    if not data:
        return -100.0
    printable = sum(1 for b in data if b in (9, 10, 13) or 32 <= b <= 126)
    return (printable / len(data)) * 100 - errors * 80 - (25 if len(data) < 4 else 0)


def preview_data(data):
    s = ""
    for b in data[:40]:
        if 32 <= b <= 126:
            s += chr(b)
        elif b == 10:
            s += "\\n"
        elif b == 13:
            s += "\\r"
        else:
            s += "\\x%02X" % b
    return s or "（无数据）"


class SerialApp:
    def __init__(self, root):
        self.root = root
        self.root.title("串口调试助手 · Python")
        self.root.geometry("1220x780")
        self.root.minsize(980, 640)

        self.ser = None
        self.read_thread = None
        self.running = False
        self.queue = queue.Queue()
        self.port_map = {}
        self.rx_bytes = 0
        self.tx_bytes = 0
        self.errors = 0
        self.rx_log = ""
        self.decoder = None
        self.decoder_enc = None
        self.history = []
        self.hist_index = -1
        self.draft = ""
        self.loop_job = None
        self.scanning = False
        self.scan_abort = False
        self.scan_results = []
        self.scan_win = None
        self.scan_tree = None
        self.scan_progress = None
        self.scan_cancel_btn = None

        self.style = ttk.Style()
        if "clam" in self.style.theme_names():
            self.style.theme_use("clam")
        self.style.configure(".", font=("Microsoft YaHei UI", 10))
        self.style.configure("TButton", padding=4)
        self.style.configure("Accent.TButton", foreground="#ffffff", background="#2563eb")
        self.style.map("Accent.TButton", background=[("active", "#1d4ed8")])

        self._build_ui()
        self.refresh_ports()
        self.update_ui()
        self.root.after(40, self.pump)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    # ---------- UI ----------
    def _build_ui(self):
        conn = ttk.LabelFrame(self.root, text="串口设置", padding=8)
        conn.pack(fill="x", padx=10, pady=(10, 4))

        ttk.Label(conn, text="端口").grid(row=0, column=0, sticky="w", padx=(0, 6))
        self.port_combo = ttk.Combobox(conn, width=46, state="readonly")
        self.port_combo.grid(row=0, column=1, sticky="ew")
        ttk.Button(conn, text="刷新", command=self.refresh_ports, width=7).grid(row=0, column=2, padx=5)
        self.btn_open = ttk.Button(conn, text="打开串口", command=self.toggle_port, width=13)
        self.btn_open.grid(row=0, column=3, padx=5)

        labels = [("波特率", 0), ("数据位", 2), ("校验位", 4), ("停止位", 6), ("流控", 8)]
        for text, col in labels:
            ttk.Label(conn, text=text).grid(row=1, column=col, sticky="w", padx=(0, 5), pady=(8, 0))
        self.baud_combo = ttk.Combobox(conn, values=COMMON_BAUDS, width=10)
        self.baud_combo.set("115200")
        self.baud_combo.grid(row=1, column=1, sticky="w", pady=(8, 0))

        self.bits_combo = ttk.Combobox(conn, values=["5", "6", "7", "8"], width=5, state="readonly")
        self.bits_combo.set("8")
        self.bits_combo.grid(row=1, column=3, sticky="w", pady=(8, 0))
        self.parity_combo = ttk.Combobox(conn, values=list(PARITY_MAP.keys()), width=12, state="readonly")
        self.parity_combo.set("无 (None)")
        self.parity_combo.grid(row=1, column=5, sticky="w", pady=(8, 0))
        self.stop_combo = ttk.Combobox(conn, values=["1", "2"], width=4, state="readonly")
        self.stop_combo.set("1")
        self.stop_combo.grid(row=1, column=7, sticky="w", pady=(8, 0))
        self.flow_combo = ttk.Combobox(conn, values=["无", "硬件 RTS/CTS"], width=15, state="readonly")
        self.flow_combo.set("无")
        self.flow_combo.grid(row=1, column=9, sticky="w", pady=(8, 0))
        self.btn_scan = ttk.Button(conn, text="扫描波特率…", command=self.scan_baud, width=14)
        self.btn_scan.grid(row=1, column=10, sticky="w", padx=8, pady=(8, 0))
        conn.columnconfigure(1, weight=1)

        # 诊断提示区（默认隐藏）
        self.diag = ttk.LabelFrame(self.root, text="诊断信息", padding=8)
        self.diag_label = tk.Label(self.diag, text="", justify="left", anchor="w",
                                   wraplength=1120, foreground="#991b1b",
                                   font=("Microsoft YaHei UI", 9), bg="#fef2f2")
        self.diag_label.pack(fill="x")
        diag_btns = ttk.Frame(self.diag)
        diag_btns.pack(fill="x", pady=(6, 0))
        ttk.Button(diag_btns, text="扫描波特率…", command=self.scan_baud, width=14).pack(side="left")
        ttk.Button(diag_btns, text="关闭提示", command=self.hide_diag, width=10).pack(side="left", padx=6)
        self.diag.pack_forget()

        paned = ttk.PanedWindow(self.root, orient="horizontal")
        paned.pack(fill="both", expand=True, padx=10, pady=4)

        left = ttk.Frame(paned)
        right = ttk.Frame(paned)
        paned.add(left, weight=3)
        paned.add(right, weight=2)

        # 接收区
        rx_bar = ttk.Frame(left)
        rx_bar.pack(fill="x", pady=(0, 6))
        ttk.Label(rx_bar, text="显示").pack(side="left")
        self.rx_mode = ttk.Combobox(rx_bar, values=["文本", "HEX"], width=7, state="readonly")
        self.rx_mode.set("文本")
        self.rx_mode.pack(side="left", padx=(4, 10))
        ttk.Label(rx_bar, text="编码").pack(side="left")
        self.encoding_combo = ttk.Combobox(rx_bar, values=ENCODINGS, width=12, state="readonly")
        self.encoding_combo.set("utf-8")
        self.encoding_combo.pack(side="left", padx=(4, 10))
        self.var_time = tk.BooleanVar(value=False)
        self.var_offset = tk.BooleanVar(value=False)
        self.var_tx_echo = tk.BooleanVar(value=True)
        self.var_scroll = tk.BooleanVar(value=True)
        for text, var in [("时间戳", self.var_time), ("HEX偏移", self.var_offset),
                          ("显示发送", self.var_tx_echo), ("自动滚动", self.var_scroll)]:
            ttk.Checkbutton(rx_bar, text=text, variable=var).pack(side="left", padx=(0, 8))
        ttk.Button(rx_bar, text="保存日志", command=self.save_log, width=10).pack(side="right", padx=3)
        ttk.Button(rx_bar, text="计数清零", command=self.reset_counters, width=10).pack(side="right", padx=3)
        ttk.Button(rx_bar, text="清空显示", command=self.clear_rx, width=10).pack(side="right", padx=3)

        rx_wrap = ttk.Frame(left)
        rx_wrap.pack(fill="both", expand=True)
        self.rx_text = tk.Text(rx_wrap, wrap="word", height=22, font=("Consolas", 10),
                               bg="#fbfcfe", fg="#1f2937", relief="solid", bd=1,
                               insertbackground="#1f2937")
        rx_scroll = ttk.Scrollbar(rx_wrap, orient="vertical", command=self.rx_text.yview)
        self.rx_text.configure(yscrollcommand=rx_scroll.set)
        rx_scroll.pack(side="right", fill="y")
        self.rx_text.pack(side="left", fill="both", expand=True)
        self.rx_text.tag_configure("tx", foreground="#2563eb")
        self.rx_text.tag_configure("err", foreground="#dc2626", font=("Consolas", 10, "bold"))
        self.rx_text.tag_configure("sys", foreground="#6b7280")
        self.append_rx("等待接收数据…\n", "sys")

        # 发送区
        tx_bar = ttk.Frame(right)
        tx_bar.pack(fill="x", pady=(0, 6))
        ttk.Label(tx_bar, text="格式").pack(side="left")
        self.tx_mode = ttk.Combobox(tx_bar, values=["文本", "HEX"], width=7, state="readonly")
        self.tx_mode.set("文本")
        self.tx_mode.pack(side="left", padx=(4, 10))
        ttk.Label(tx_bar, text="结尾").pack(side="left")
        self.eol_combo = ttk.Combobox(tx_bar, values=list(EOL_MAP.keys()), width=9, state="readonly")
        self.eol_combo.set("CR+LF")
        self.eol_combo.pack(side="left", padx=(4, 0))

        self.tx_text = tk.Text(right, height=9, font=("Consolas", 10), bg="#fbfcfe",
                               fg="#1f2937", relief="solid", bd=1, insertbackground="#1f2937")
        self.tx_text.pack(fill="both", expand=True)
        self.tx_text.bind("<Control-Return>", lambda e: self.send_data())
        self.tx_text.bind("<Up>", self.on_history_up)
        self.tx_text.bind("<Down>", self.on_history_down)

        tx_actions = ttk.Frame(right)
        tx_actions.pack(fill="x", pady=(8, 0))
        self.btn_send = ttk.Button(tx_actions, text="发送数据", command=self.send_data, width=11)
        self.btn_send.pack(side="left")
        self.btn_loop = ttk.Button(tx_actions, text="循环发送", command=self.toggle_loop, width=11)
        self.btn_loop.pack(side="left", padx=6)
        ttk.Label(tx_actions, text="间隔 ms").pack(side="left", padx=(6, 4))
        self.interval_var = tk.StringVar(value="1000")
        ttk.Spinbox(tx_actions, from_=50, to=60000, increment=50, textvariable=self.interval_var,
                    width=7).pack(side="left")
        ttk.Label(tx_actions, text="Ctrl+Enter 发送", foreground="#9ca3af").pack(side="right")

        quick = ttk.LabelFrame(right, text="快捷指令（支持 \\r \\n \\t \\xHH）", padding=6)
        quick.pack(fill="x", pady=(10, 0))
        self.quick_entries = []
        defaults = ["AT\\r\\n", "\\r\\n", "hello", "\\x00\\x01\\x02"]
        self.quick_buttons = []
        for idx, default in enumerate(defaults):
            row = ttk.Frame(quick)
            row.pack(fill="x", pady=2)
            entry = ttk.Entry(row, font=("Consolas", 9))
            entry.insert(0, default)
            entry.pack(side="left", fill="x", expand=True)
            self.quick_entries.append(entry)
            btn = ttk.Button(row, text="发送", width=6,
                             command=lambda n=idx: self.send_quick(n))
            btn.pack(side="left", padx=5)
            self.quick_buttons.append(btn)

        status = ttk.Frame(self.root, padding=(10, 6))
        status.pack(fill="x", side="bottom")
        self.status_vars = {}
        for i, key in enumerate(["状态", "端口", "参数", "RX", "TX", "读取错误", "消息"]):
            ttk.Label(status, text=key + "：").grid(row=0, column=i * 2, sticky="w", padx=(0, 3))
            var = tk.StringVar(value="—" if key != "消息" else "")
            ttk.Label(status, textvariable=var, foreground="#2563eb").grid(
                row=0, column=i * 2 + 1, sticky="w", padx=(0, 16))
            self.status_vars[key] = var

    # ---------- 工具方法 ----------
    def set_msg(self, text):
        self.status_vars["消息"].set(text)

    def update_status(self):
        self.status_vars["RX"].set(self._size(self.rx_bytes))
        self.status_vars["TX"].set(self._size(self.tx_bytes))
        self.status_vars["读取错误"].set(str(self.errors))

    @staticmethod
    def _size(n):
        if n < 1024:
            return "%d B" % n
        if n < 1024 * 1024:
            return "%.1f KB" % (n / 1024)
        return "%.2f MB" % (n / 1024 / 1024)

    def update_ui(self):
        opened = bool(self.ser and self.ser.is_open)
        self.btn_open.configure(text="关闭串口" if opened else "打开串口")
        state = "disabled" if opened or self.scanning else "normal"
        for widget in [self.baud_combo, self.bits_combo, self.parity_combo,
                       self.stop_combo, self.flow_combo, self.btn_scan]:
            widget.configure(state=state)
        self.port_combo.configure(state="disabled" if (opened or self.scanning) else "readonly")
        send_state = "normal" if opened else "disabled"
        self.btn_send.configure(state=send_state)
        self.btn_loop.configure(state=send_state)
        for btn in self.quick_buttons:
            btn.configure(state=send_state)
        if not opened:
            self.stop_loop()
        self.status_vars["状态"].set("已连接" if opened else ("扫描中" if self.scanning else "未连接"))
        self.status_vars["端口"].set(self.port_combo.get().split(" - ")[0] if opened else "—")
        self.status_vars["参数"].set(
            "%s %s%s%s" % (self.baud_combo.get(), self.bits_combo.get(),
                           self.parity_combo.get()[0].upper(), self.stop_combo.get()) if opened else "—")
        self.update_status()

    def append_rx(self, text, tag=None):
        self.rx_text.configure(state="normal")
        if tag:
            self.rx_text.insert("end", text, tag)
        else:
            self.rx_text.insert("end", text)
        lines = int(self.rx_text.index("end-1c").split(".")[0])
        if lines > 6000:
            self.rx_text.delete("1.0", "1000.0")
        if self.var_scroll.get():
            self.rx_text.see("end")
        self.rx_text.configure(state="disabled")
        self.rx_log += text
        if len(self.rx_log) > 1000000:
            self.rx_log = self.rx_log[-500000:]

    def clear_rx(self):
        self.rx_text.configure(state="normal")
        self.rx_text.delete("1.0", "end")
        self.rx_text.configure(state="disabled")
        self.rx_log = ""

    def reset_counters(self):
        self.rx_bytes = 0
        self.tx_bytes = 0
        self.errors = 0
        self.update_status()

    def show_diag(self, message):
        low = message.lower()
        if "break" in low:
            title = "线路 Break（持续低电平）"
            tips = ("Break 表示接收线被持续拉低。常见原因：设备实际波特率远高于当前设置、TX/RX 接反或短接、"
                    "双方未共地、TTL 与 RS232 电平不匹配，或设备正在发送 LIN / DMX 等 break 信号。建议点“扫描波特率…”。")
        elif any(k in low for k in ("framing", "frame", "parity", "帧", "校验")):
            title = "帧错误 / 串口参数不匹配"
            tips = ("优先核对波特率，其次核对校验位 / 数据位 / 停止位；确认 TX 与 RX 交叉相接、双方共地、"
                    "电平一致（TTL 与 RS232 需电平转换）。若收到乱码，请把接收区切到 HEX 模式确认是否为编码问题。")
        else:
            title = "串口读取错误"
            tips = "请检查设备连接、波特率与接线，或点击“扫描波特率…”自动探测。"
        self.diag_label.configure(text="【%s】%s\n%s" % (title, message, tips))
        self.diag.pack(fill="x", padx=10, pady=4)

    def hide_diag(self):
        self.diag.pack_forget()

    # ---------- 串口操作 ----------
    def refresh_ports(self):
        self.port_map = {}
        items = []
        for p in list_ports.comports():
            label = p.device + (" - " + p.description if p.description else "")
            self.port_map[label] = p.device
            items.append(label)
        self.port_combo["values"] = items
        if items:
            self.port_combo.current(0)
        else:
            self.port_combo.set("")

    def selected_device(self):
        return self.port_map.get(self.port_combo.get(), "")

    def serial_kwargs(self, baud):
        return dict(
            port=self.selected_device(),
            baudrate=int(baud),
            bytesize=int(self.bits_combo.get()),
            parity=PARITY_MAP[self.parity_combo.get()],
            stopbits=STOP_MAP[self.stop_combo.get()],
            xonxoff=(self.flow_combo.get() == "XON/XOFF"),
            rtscts=(self.flow_combo.get() == "硬件 RTS/CTS"),
            timeout=0.2,
            write_timeout=1.0,
        )

    def toggle_port(self):
        if self.ser and self.ser.is_open:
            self.close_port()
        else:
            self.open_port()

    def open_port(self):
        if self.scanning:
            return
        device = self.selected_device()
        if not device:
            messagebox.showwarning("提示", "请先选择串口端口")
            return
        try:
            baud = int(self.baud_combo.get())
            kwargs = self.serial_kwargs(baud)
            if kwargs["rtscts"] is False:
                kwargs["dsrdtr"] = False
            ser = serial.Serial(**kwargs)
        except Exception as exc:
            messagebox.showerror("打开串口失败", str(exc))
            return
        self.ser = ser
        self.running = True
        self.decoder = None
        self.decoder_enc = None
        self.hide_diag()
        self.append_rx("\n--- 串口已打开 %s ---\n" % now_stamp(), "sys")
        self.read_thread = threading.Thread(target=self.read_loop, args=(ser,), daemon=True)
        self.read_thread.start()
        self.update_ui()
        self.set_msg("串口已打开")

    def close_port(self, from_error=False):
        self.stop_loop()
        self.running = False
        if self.ser is not None:
            try:
                self.ser.close()
            except Exception:
                pass
        if self.read_thread and self.read_thread.is_alive():
            self.read_thread.join(timeout=1.0)
        self.read_thread = None
        self.ser = None
        self.append_rx("\n--- 串口已关闭 %s ---\n" % now_stamp(), "sys")
        self.update_ui()
        if not from_error:
            self.set_msg("串口已关闭")

    def read_loop(self, ser):
        while self.running and ser.is_open:
            try:
                data = ser.read(4096)
            except Exception as exc:
                if self.running:
                    self.queue.put(("error", str(exc)))
                break
            if data and self.running:
                self.queue.put(("data", bytes(data)))

    # ---------- 接收处理 ----------
    def on_data(self, data):
        self.rx_bytes += len(data)
        if self.rx_mode.get() == "HEX":
            text = format_hex(data, self.var_offset.get())
            if self.var_time.get():
                text = "[%s]\n%s" % (now_stamp(), text)
        else:
            enc = self.encoding_combo.get()
            if self.decoder is None or self.decoder_enc != enc:
                self.decoder = codecs.getincrementaldecoder(enc)(errors="replace")
                self.decoder_enc = enc
            text = self.decoder.decode(data)
            if self.var_time.get():
                text = "[%s] %s" % (now_stamp(), text)
        self.append_rx(text)
        self.update_status()

    def on_error(self, message):
        self.errors += 1
        self.update_status()
        self.queue.put(("flush_decoder", None))
        self.append_rx("\n[!] 读取错误：%s\n" % message, "err")
        self.show_diag(message)
        if self.running:
            self.close_port(from_error=True)
        self.set_msg("读取中断：" + message)

    # ---------- 发送处理 ----------
    def build_payload(self, text, mode, add_eol):
        if mode == "HEX":
            return parse_hex(text)
        return (text + (EOL_MAP[self.eol_combo.get()] if add_eol else "")).encode("utf-8", errors="replace")

    def write_bytes(self, data):
        if not (self.ser and self.ser.is_open):
            messagebox.showwarning("提示", "请先打开串口")
            return False
        if not data:
            self.set_msg("发送内容为空")
            return False
        try:
            self.ser.write(data)
        except Exception as exc:
            self.queue.put(("error", str(exc)))
            return False
        self.tx_bytes += len(data)
        if self.var_tx_echo.get():
            if self.rx_mode.get() == "HEX":
                echo = format_hex(data, self.var_offset.get())
            else:
                echo = data.decode(self.encoding_combo.get(), errors="replace")
            self.append_rx("[TX %s] %s" % (now_stamp(), echo), "tx")
        self.update_status()
        return True

    def send_data(self, record=True):
        raw = self.tx_text.get("1.0", "end-1c")
        try:
            data = self.build_payload(raw, self.tx_mode.get(), True)
        except ValueError as exc:
            messagebox.showerror("发送格式错误", str(exc))
            return
        if self.write_bytes(data) and record:
            self.add_history(raw)

    def send_quick(self, index):
        try:
            data = parse_escapes(self.quick_entries[index].get())
        except ValueError as exc:
            messagebox.showerror("快捷指令错误", str(exc))
            return
        self.write_bytes(data)

    def add_history(self, text):
        if text and (not self.history or self.history[-1] != text):
            self.history.append(text)
            if len(self.history) > 50:
                self.history.pop(0)
        self.hist_index = -1

    def set_tx_text(self, text):
        self.tx_text.delete("1.0", "end")
        self.tx_text.insert("1.0", text)

    def on_history_up(self, event):
        if not self.history:
            return None
        if self.hist_index == -1:
            self.draft = self.tx_text.get("1.0", "end-1c")
            self.hist_index = len(self.history) - 1
        else:
            self.hist_index = max(0, self.hist_index - 1)
        self.set_tx_text(self.history[self.hist_index])
        return "break"

    def on_history_down(self, event):
        if self.hist_index == -1:
            return None
        if self.hist_index < len(self.history) - 1:
            self.hist_index += 1
            self.set_tx_text(self.history[self.hist_index])
        else:
            self.hist_index = -1
            self.set_tx_text(self.draft)
        return "break"

    def toggle_loop(self):
        if self.loop_job is not None:
            self.stop_loop()
            return
        if not (self.ser and self.ser.is_open):
            messagebox.showwarning("提示", "请先打开串口")
            return
        self.btn_loop.configure(text="停止循环")
        self.loop_tick()

    def loop_tick(self):
        if not (self.ser and self.ser.is_open):
            self.stop_loop()
            return
        self.send_data(record=False)
        try:
            ms = max(50, int(self.interval_var.get()))
        except ValueError:
            ms = 1000
        self.loop_job = self.root.after(ms, self.loop_tick)

    def stop_loop(self):
        if self.loop_job is not None:
            try:
                self.root.after_cancel(self.loop_job)
            except Exception:
                pass
        self.loop_job = None
        if hasattr(self, "btn_loop"):
            self.btn_loop.configure(text="循环发送")

    # ---------- 日志 ----------
    def save_log(self):
        if not self.rx_log:
            messagebox.showinfo("提示", "接收区暂无内容")
            return
        path = filedialog.asksaveasfilename(
            title="保存接收日志",
            defaultextension=".txt",
            initialfile="serial-log-%s.txt" % file_stamp(),
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")],
        )
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as fh:
                fh.write(self.rx_log)
            self.set_msg("日志已保存：" + path)
        except Exception as exc:
            messagebox.showerror("保存失败", str(exc))

    # ---------- 波特率扫描 ----------
    def scan_baud(self):
        if self.scanning:
            self.scan_abort = True
            return
        device = self.selected_device()
        if not device:
            messagebox.showwarning("提示", "请先选择串口端口")
            return
        if self.ser and self.ser.is_open:
            self.close_port()

        self.scanning = True
        self.scan_abort = False
        self.scan_results = []
        self.update_ui()

        win = tk.Toplevel(self.root)
        win.title("波特率扫描")
        win.geometry("620x400")
        win.transient(self.root)
        self.scan_win = win
        win.protocol("WM_DELETE_WINDOW", self.cancel_scan)

        ttk.Label(win, text="正在依次尝试常见波特率（约 4 秒）…",
                  padding=(10, 8)).pack(fill="x")
        self.scan_progress = ttk.Label(win, text="准备中…", foreground="#2563eb", padding=(10, 0))
        self.scan_progress.pack(fill="x")
        tree_frame = ttk.Frame(win, padding=(10, 6))
        tree_frame.pack(fill="both", expand=True)
        self.scan_tree = ttk.Treeview(tree_frame, columns=("baud", "bytes", "preview"), show="headings", height=12)
        self.scan_tree.heading("baud", text="波特率")
        self.scan_tree.heading("bytes", text="接收字节")
        self.scan_tree.heading("preview", text="数据预览")
        self.scan_tree.column("baud", width=100, anchor="center")
        self.scan_tree.column("bytes", width=110, anchor="center")
        self.scan_tree.column("preview", width=380)
        sb = ttk.Scrollbar(tree_frame, orient="vertical", command=self.scan_tree.yview)
        self.scan_tree.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.scan_tree.pack(side="left", fill="both", expand=True)
        self.scan_tree.bind("<<TreeviewSelect>>", self.apply_selected_baud)
        self.scan_cancel_btn = ttk.Button(win, text="取消扫描", command=self.cancel_scan, width=12)
        self.scan_cancel_btn.pack(pady=(0, 10))

        threading.Thread(target=self.scan_worker, args=(device,), daemon=True).start()

    def scan_worker(self, device):
        base = dict(
            port=device,
            bytesize=int(self.bits_combo.get()),
            parity=PARITY_MAP[self.parity_combo.get()],
            stopbits=STOP_MAP[self.stop_combo.get()],
            xonxoff=False,
            rtscts=False,
            timeout=0.1,
            write_timeout=0.2,
        )
        for rate in BAUD_CANDIDATES:
            if self.scan_abort:
                break
            self.queue.put(("scan_progress", "正在尝试 %d …" % rate))
            data = b""
            errors = 0
            try:
                probe = serial.Serial(baudrate=rate, **base)
                deadline = time.time() + 0.35
                while time.time() < deadline and not self.scan_abort:
                    chunk = probe.read(256)
                    if chunk:
                        data += chunk
                    if len(data) >= 64:
                        break
                probe.close()
            except Exception:
                errors += 1
            self.queue.put(("scan_result", (
                rate, len(data), errors, preview_data(data), score_data(data, errors))))
        self.queue.put(("scan_done", None))

    def cancel_scan(self):
        if self.scanning:
            self.scan_abort = True
        elif self.scan_win is not None:
            self.scan_win.destroy()
            self.scan_win = None

    def apply_selected_baud(self, event=None):
        sel = self.scan_tree.selection()
        if not sel:
            return
        rate = self.scan_tree.item(sel[0], "values")[0]
        self.baud_combo.set(str(rate))
        self.set_msg("已应用波特率 %s" % rate)

    def finish_scan(self):
        if not self.scan_results:
            self.set_msg("扫描结束：未收到数据")
        else:
            best = max(self.scan_results, key=lambda r: r[4])
            if best[4] > 0:
                self.baud_combo.set(str(best[0]))
                self.set_msg("扫描完成：推荐 %d，已自动应用" % best[0])
            else:
                self.set_msg("扫描完成：未收到可识别数据，请检查接线")
        self.scanning = False
        self.update_ui()
        if self.scan_win is not None and self.scan_progress is not None:
            self.scan_progress.configure(text="扫描完成，点击任意行应用该波特率")
        if self.scan_win is not None and self.scan_cancel_btn is not None:
            self.scan_cancel_btn.configure(text="关闭", command=self.cancel_scan)

    # ---------- 事件泵 ----------
    def pump(self):
        try:
            while True:
                kind, payload = self.queue.get_nowait()
                if kind == "data":
                    self.on_data(payload)
                elif kind == "error":
                    self.on_error(payload)
                elif kind == "flush_decoder":
                    self.decoder = None
                    self.decoder_enc = None
                elif kind == "scan_progress":
                    if self.scan_win is not None and self.scan_progress is not None:
                        self.scan_progress.configure(text=payload)
                elif kind == "scan_result":
                    self.scan_results.append(payload)
                    if self.scan_win is not None and self.scan_tree is not None:
                        rate, count, errors, preview, score = payload
                        self.scan_tree.insert("", "end", values=(
                            str(rate), "%d B%s" % (count, (" / 错 %d" % errors) if errors else ""), preview))
                elif kind == "scan_done":
                    if self.scan_win is not None and self.scan_tree is not None:
                        ordered = sorted(self.scan_results, key=lambda r: r[4], reverse=True)
                        for item in self.scan_tree.get_children():
                            self.scan_tree.delete(item)
                        for rate, count, errors, preview, score in ordered:
                            self.scan_tree.insert("", "end", values=(
                                str(rate), "%d B%s" % (count, (" / 错 %d" % errors) if errors else ""), preview))
                    self.finish_scan()
        except queue.Empty:
            pass
        self.root.after(40, self.pump)

    def on_close(self):
        self.stop_loop()
        if self.ser and self.ser.is_open:
            self.close_port()
        self.root.destroy()


def main():
    root = tk.Tk()
    SerialApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
