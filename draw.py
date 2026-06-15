#!/usr/bin/env python3
"""
a node/graph sketcher that runs *inside* the terminal.

A BOARD holds draw-nodes. Each node opens full-screen as a CANVAS (a braille
vector editor); collapse it and it becomes a small box on the board showing a
live mini-preview of its drawing. Nodes can be dragged around and linked with
edges to build a graph / mind-map.

Rendering uses a braille sub-cell grid (each character cell = 2x4 dots, 8x the
resolution of text) and pixel-level mouse tracking on terminals that support
SGR-Pixels mode (WezTerm, kitty, foot, ghostty, contour); falls back to
cell-level elsewhere (e.g. iTerm2, which reports a pixel cell size but doesn't
implement ?1016). Override with DRAW_PIXEL_MOUSE=1/0.

BOARD controls
  mouse        click select   drag move   double-click [↗] tab to open
  keys         n new node   Enter open   d delete   l link   r rename
               Tab cycle   s save   o open   q quit   ? help

CANVAS controls
  drawing      left-drag draws   right-drag erases
  tools        f freehand  l line  r rectangle  i ellipse  a arrow  e eraser
  color        1-8 pick palette color
  eraser       [ shrink   ] grow   scroll-wheel resizes (a ring shows the area)
  history      u undo   R redo   c clear
  files        x export this node to .svg
  misc         b / Tab back to board   ? help

Usage:  python3 draw.py [boardfile]
No dependencies — standard library only.
"""
import sys
import os
import termios
import tty
import struct
import fcntl
import re
import math
import json
import signal
import time

USAGE = """draw — a node/graph terminal sketcher

usage: python3 draw.py [options] [name]

options:
  -q, --canvas, --draw  open straight into a single canvas (no board)
  -c, --config PATH     settings file to load/save (default: ~/.draw.json;
                        also honoured via the DRAW_CONFIG env var)
  -h, --help            show this help

  name                  default board/file basename (default: draw)

startup:
  On launch the board named by the "Auto-open file name" setting (or the
  given name) is opened from the "Auto-open directory" (or the open/work
  directory). Toggle "Auto-open a board on launch" in Settings to disable.

modes:
  board    nodes you can draw in, link, and arrange (default)
  canvas    one full-screen canvas; back/quit exits
"""

ESC = "\x1b"
BRAILLE_BASE = 0x2800
PIXEL_MAP = ((0x01, 0x08),   # dot bit for [y_in_cell][x_in_cell]
             (0x02, 0x10),
             (0x04, 0x20),
             (0x40, 0x80))
MOUSE_RE = re.compile(r"\x1b\[<(\d+);(\d+);(\d+)([Mm])")

PALETTE = [
    ("white",  (230, 230, 230)),
    ("red",    (235,  77,  75)),
    ("orange", (240, 147,  43)),
    ("yellow", (245, 222,  80)),
    ("green",  (106, 176,  76)),
    ("cyan",   (34, 166, 179)),
    ("blue",   (72, 126, 236)),
    ("purple", (190, 103, 220)),
]
TOOLS = {"f": "free", "l": "line", "r": "rect",
         "i": "ellipse", "a": "arrow", "e": "erase"}
DEFAULT_ERASE_R = 3
MIN_ERASE_R, MAX_ERASE_R = 1, 24
CURSOR_COLOR = (130, 130, 140)
PREVIEW_COLOR = (200, 205, 215)
EDGE_COLOR = (95, 95, 115)
NODE_COLOR = (150, 150, 165)
SEL_COLOR = (245, 205, 90)
LINK_COLOR = (120, 200, 120)
HOVER_COLOR = (90, 200, 230)
MENU_BORDER = (205, 205, 220)
MENU_TEXT = (225, 225, 235)
TAB_COLOR = (110, 180, 215)
TAB_HOVER = (245, 205, 90)
SELECT_HL = (120, 220, 255)
MARQUEE_COLOR = (180, 180, 205)        # selection rectangle outline
BAR_BG, BAR_FG, PROMPT_BG = 236, 252, 24
SETTINGS_BG = 22
NODE_W, NODE_H = 22, 8                  # node box size in cells
TAB_LABEL = "[↗]"
DOUBLE_CLICK_S = 0.4                    # max gap between the two tab clicks

BOX_TL, BOX_TR, BOX_BL, BOX_BR = "┌", "┐", "└", "┘"
BOX_H, BOX_V = "─", "│"

CONFIG_PATH = os.path.expanduser("~/.draw.json")

# (action, label, default key)
BOARD_BIND = [
    ("new_node", "New node", "n"),
    ("new_board", "New board", "N"),
    ("delete", "Delete node", "d"),
    ("link", "Link", "l"),
    ("rename", "Rename", "r"),
    ("save", "Save board", "s"),
    ("open", "Open board", "o"),
    ("boards", "Browse boards", "b"),
    ("settings", "Settings", ","),
]
CANVAS_BIND = [
    ("free", "Tool: freehand", "f"),
    ("line", "Tool: line", "l"),
    ("rect", "Tool: rectangle", "r"),
    ("ellipse", "Tool: ellipse", "i"),
    ("arrow", "Tool: arrow", "a"),
    ("erase", "Tool: eraser", "e"),
    ("select", "Tool: select / move", "v"),
    ("undo", "Undo", "u"),
    ("redo", "Redo", "R"),
    ("clear", "Clear canvas", "c"),
    ("export", "Export SVG", "x"),
    ("back", "Back to board", "b"),
]
TOOL_ACTIONS = ("select", "free", "line", "rect", "ellipse", "arrow", "erase")


def default_keymap():
    km = {}
    for a, _, k in BOARD_BIND:
        km["board." + a] = k
    for a, _, k in CANVAS_BIND:
        km["canvas." + a] = k
    return km


def default_config():
    return {
        "work_dir": "", "save_dir": "", "open_dir": "",
        "autoload": True, "autoload_file": "", "autoload_dir": "",
        "last_board": "",
        "hover_recolor_selected": False,
        "show_hint_labels": True,
        "hide_ui": False,
        "default_tool": "free", "default_color": 0, "default_erase": 3,
        "keymap": default_keymap(),
    }


def line_dots(x0, y0, x1, y1):
    """Bresenham — yields integer points between two coordinates"""
    x0, y0, x1, y1 = int(round(x0)), int(
        round(y0)), int(round(x1)), int(round(y1))
    dx, dy = abs(x1 - x0), -abs(y1 - y0)
    sx = 1 if x0 < x1 else -1
    sy = 1 if y0 < y1 else -1
    err = dx + dy
    while True:
        yield (x0, y0)
        if x0 == x1 and y0 == y1:
            break
        e2 = 2 * err
        if e2 >= dy:
            err += dy
            x0 += sx
        if e2 <= dx:
            err += dx
            y0 += sy


def circle_dots(cx, cy, r):
    """Midpoint circle outline — yields the dots forming a ring of radius r"""
    if r <= 0:
        yield (cx, cy)
        return
    x, y, err = r, 0, 1 - r
    pts = set()
    while x >= y:
        for px, py in ((x, y), (y, x), (-y, x), (-x, y),
                       (-x, -y), (-y, -x), (y, -x), (x, -y)):
            pts.add((cx + px, cy + py))
        y += 1
        if err < 0:
            err += 2 * y + 1
        else:
            x -= 1
            err += 2 * (y - x) + 1
    yield from pts


def get_winsize(fd):
    try:
        buf = fcntl.ioctl(fd, termios.TIOCGWINSZ,
                          struct.pack("HHHH", 0, 0, 0, 0))
        rows, cols, xpix, ypix = struct.unpack("HHHH", buf)
        return rows, cols, xpix, ypix
    except Exception:
        return 24, 80, 0, 0


def pixel_mouse_supported():
    """Does this terminal implement SGR-Pixel mouse reporting (CSI ?1016)?

    Several terminals (notably iTerm2) report a pixel cell size via
    TIOCGWINSZ but ignore ?1016 and keep sending *cell* coordinates. Trusting
    pixel mode there scales those small cell numbers as if they were pixels,
    which collapses the cursor toward the top-left and desyncs it from the
    drawing. So only enable pixel mode on terminals known to support ?1016.
    Set DRAW_PIXEL_MOUSE=1/0 to force it on/off.
    """
    force = os.environ.get("DRAW_PIXEL_MOUSE", "").strip().lower()
    if force in ("1", "on", "true", "yes"):
        return True
    if force in ("0", "off", "false", "no"):
        return False
    env = os.environ
    term = env.get("TERM", "")
    prog = env.get("TERM_PROGRAM", "")
    if prog == "WezTerm" or env.get("WEZTERM_EXECUTABLE"):
        return True
    if "kitty" in term or env.get("KITTY_WINDOW_ID"):
        return True
    if term.startswith("foot"):
        return True
    if prog == "contour" or env.get("CONTOUR_VERSION"):
        return True
    if prog == "ghostty" or env.get("GHOSTTY_RESOURCES_DIR"):
        return True
    return False


def rgbhex(c):
    return "#%02x%02x%02x" % (c[0], c[1], c[2])


class App:
    def __init__(self, basename=".draw", canvas=False, config_path=None):
        self.fd = sys.stdin.fileno()
        self.canvas = canvas
        self.config_path = (os.path.expanduser(config_path)
                            if config_path else CONFIG_PATH)
        self._measure()
        self._disk_cache = {}
        self.cfg = self.load_config()
        self.rebuild_keymaps()

        # ---- board state ----
        # each: {id,title,bx,by,w,h,shapes,hist,hidx,_prev}
        self.nodes = []
        self.edges = []         # each: [id_a, id_b]
        self.next_id = 1
        self.mode = "board"
        self.active_node = None
        self.selected = None
        self.dragging = None
        self.link_from = None
        self.hover = None
        self.hover_tab = None           # node id whose open-tab the mouse is over
        self.last_tab_click = (None, 0.0)   # (node id, time) for double-click
        self.menu = None
        self.press_cell = (0, 0)
        self.press_moved = False
        self.mouse_cell = (self.cols // 2, self.rows // 2)
        self.txt = {}           # text-cell screen cache for board rendering

        # ---- per-canvas drawing state (loaded from the active node) ----
        self.shapes = []
        self.history = [[]]
        self.hidx = 0
        self.base = {}
        self.displayed = {}     # braille screen cache for canvas rendering
        self.overlay = {}
        self.overlay_prev = set()

        self.tool = self.cfg.get("default_tool", "free")
        ci = self.cfg.get("default_color", 0) % len(PALETTE)
        self.color_name, self.color = PALETTE[ci]
        self.erase_r = self.cfg.get("default_erase", DEFAULT_ERASE_R)
        self.active = False
        self.stroke_tool = "free"
        self.start = (0, 0)
        self.mouse_dot = (self.dw // 2, self.dh // 2)
        self.cur_pts = []

        # ---- selection (select tool) ----
        self.sel_indices = set()
        self.sel_mode = None            # None | "marquee" | "move"
        self.sel_start = (0, 0)
        self.sel_last = (0, 0)
        self.sel_bbox = None
        self.move_base = None

        # ---- settings screen state ----
        self.settings_rows = []
        self.settings_hover = 0
        self.settings_top = 0
        self.capture_action = None

        # ---- board browser state ----
        self.board_list = []
        self.board_hover = 0
        self.board_top = 0

        self.last_name = basename
        self.prompt_mode = None
        self.prompt_buf = ""
        self.flash = ""
        self.help_open = False
        self.resized = False
        self.running = True
        self.dirty = False              # unsaved changes since last save/load
        self.quit_after_save = False
        self.confirm = None             # pending yes/no modal

    # ---- config ----
    def load_config(self):
        cfg = default_config()
        try:
            with open(self.config_path) as f:
                data = json.load(f)
            for k, v in data.items():
                if k == "keymap" and isinstance(v, dict):
                    cfg["keymap"].update(v)
                elif k in cfg:
                    cfg[k] = v
        except Exception:
            pass
        return cfg

    def save_config(self):
        try:
            d = os.path.dirname(self.config_path)
            if d:
                os.makedirs(d, exist_ok=True)
            with open(self.config_path, "w") as f:
                json.dump(self.cfg, f, indent=2)
        except Exception:
            pass

    def _tilde(self, p):
        home = os.path.expanduser("~")
        return "~" + p[len(home):] if p.startswith(home) else p

    def _remember_board(self, path):
        path = os.path.abspath(path)
        if self.cfg.get("last_board") != path:
            self.cfg["last_board"] = path
            self.save_config()

    def rebuild_keymaps(self):
        km = self.cfg["keymap"]
        self.bkeys = {km.get("board." + a, k): a for a, _, k in BOARD_BIND}
        self.ckeys = {km.get("canvas." + a, k): a for a, _, k in CANVAS_BIND}

    def _resolve(self, name, which):
        if os.path.isabs(os.path.expanduser(name)):
            return os.path.expanduser(name)
        base = self.cfg.get(which + "_dir") or self.cfg.get("work_dir") or "."
        return os.path.join(os.path.expanduser(base), name)

    def _measure(self):
        rows, cols, xpix, ypix = get_winsize(sys.stdout.fileno())
        self.cols, self.rows = cols, rows
        # reserve bottom row for status
        self.dw, self.dh = cols * 2, (rows - 1) * 4
        self.status_row = rows
        self.pixel_mode = xpix > 0 and ypix > 0 and pixel_mouse_supported()
        self.cell_px = (xpix / cols) if self.pixel_mode else 1.0
        self.cell_py = (ypix / rows) if self.pixel_mode else 1.0
        self.ppx = self.cell_px / 2
        self.ppy = self.cell_py / 4

    # ---- coordinate mapping -------------------------------------------------
    def to_dot(self, x, y):
        if self.pixel_mode:
            return int((x - 1) / self.ppx), int((y - 1) / self.ppy)
        return (x - 1) * 2, (y - 1) * 4

    def to_cell(self, x, y):
        if self.pixel_mode:
            return int((x - 1) / self.cell_px) + 1, int((y - 1) / self.cell_py) + 1
        return x, y

    # ============================ CANVAS ENGINE =============================
    def _disk_offsets(self, r):
        r = int(r)
        o = self._disk_cache.get(r)
        if o is None:
            o = [(dx, dy) for dx in range(-r, r + 1) for dy in range(-r, r + 1)
                 if dx * dx + dy * dy <= r * r]
            self._disk_cache[r] = o
        return o

    def _set(self, grid, x, y, color, touched):
        x, y = int(x), int(y)
        if not (0 <= x < self.dw and 0 <= y < self.dh):
            return
        cell = (x // 2, y // 4)
        bit = PIXEL_MAP[y % 4][x % 2]
        m = grid.get(cell, (0, None))[0]
        grid[cell] = (m | bit, color)
        touched.add(cell)

    def _unset(self, grid, x, y, touched):
        x, y = int(x), int(y)
        if not (0 <= x < self.dw and 0 <= y < self.dh):
            return
        cell = (x // 2, y // 4)
        e = grid.get(cell)
        if not e:
            return
        nm = e[0] & ~PIXEL_MAP[y % 4][x % 2]
        if nm:
            grid[cell] = (nm, e[1])
        else:
            grid.pop(cell, None)
        touched.add(cell)

    def _stamp_unset(self, grid, x, y, r, touched):
        for dx, dy in self._disk_offsets(r):
            self._unset(grid, x + dx, y + dy, touched)

    def _erase_path(self, grid, pts, r, touched):
        """Erase a disk along a polyline, striding by ~r/2"""
        if not pts:
            return
        stride = max(1, r // 2)
        self._stamp_unset(grid, pts[0][0], pts[0][1], r, touched)
        last, prev = pts[0], pts[0]
        for p in pts[1:]:
            for (x, y) in line_dots(prev[0], prev[1], p[0], p[1]):
                if abs(x - last[0]) + abs(y - last[1]) >= stride:
                    self._stamp_unset(grid, x, y, r, touched)
                    last = (x, y)
            prev = p
        self._stamp_unset(grid, prev[0], prev[1], r, touched)

    def arrow_head(self, p0, p1):
        ang = math.atan2(p1[1] - p0[1], p1[0] - p0[0])
        dist = math.hypot(p1[0] - p0[0], p1[1] - p0[1])
        length = max(4.0, min(10.0, dist / 3))
        out = []
        for da in (2.6, -2.6):                  # ~150 degrees off the shaft
            hx = p1[0] + length * math.cos(ang + da)
            hy = p1[1] + length * math.sin(ang + da)
            out.append((p1, (hx, hy)))
        return out

    def ellipse_dots(self, cx, cy, rx, ry):
        n = max(24, int(rx + ry))
        pts = []
        for i in range(n + 1):
            t = 2 * math.pi * i / n
            pts.append((cx + rx * math.cos(t), cy + ry * math.sin(t)))
        for i in range(len(pts) - 1):
            yield from line_dots(*pts[i], *pts[i + 1])

    def apply_shape(self, grid, shape):
        """Rasterize one shape into `grid`; return the set of touched cells"""
        t = shape["t"]
        color = tuple(shape["c"])
        pts = shape["p"]
        touched = set()

        def seg(a, b):
            for (x, y) in line_dots(a[0], a[1], b[0], b[1]):
                self._set(grid, x, y, color, touched)

        if t == "free":
            if len(pts) == 1:
                self._set(grid, pts[0][0], pts[0][1], color, touched)
            for i in range(len(pts) - 1):
                seg(pts[i], pts[i + 1])
        elif t == "erase":
            self._erase_path(grid, pts, shape.get(
                "r", DEFAULT_ERASE_R), touched)
        elif t == "line":
            seg(pts[0], pts[1])
        elif t == "arrow":
            seg(pts[0], pts[1])
            for a, b in self.arrow_head(pts[0], pts[1]):
                seg(a, b)
        elif t == "rect":
            (x0, y0), (x1, y1) = pts[0], pts[1]
            x0, x1 = sorted((x0, x1))
            y0, y1 = sorted((y0, y1))
            corners = [(x0, y0), (x1, y0), (x1, y1), (x0, y1)]
            for i in range(4):
                seg(corners[i], corners[(i + 1) % 4])
        elif t == "ellipse":
            (x0, y0), (x1, y1) = pts[0], pts[1]
            cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
            rx, ry = abs(x1 - x0) / 2, abs(y1 - y0) / 2
            for (x, y) in self.ellipse_dots(cx, cy, rx, ry):
                self._set(grid, x, y, color, touched)
        return touched

    def blit_cells(self, cells, target_get):
        out = []
        for cell in cells:
            cx, cy = cell
            mask, color = target_get(cell)
            cur = self.displayed.get(cell)
            if mask == 0:
                if cur is not None:
                    out.append(f"{ESC}[{cy + 1};{cx + 1}H ")
                    self.displayed.pop(cell, None)
            elif cur != (mask, color):
                ch = chr(BRAILLE_BASE + mask)
                if color:
                    r, g, b = color
                    out.append(
                        f"{ESC}[{cy + 1};{cx + 1}H{ESC}[38;2;{r};{g};{b}m{ch}")
                else:
                    out.append(f"{ESC}[{cy + 1};{cx + 1}H{ch}")
                self.displayed[cell] = (mask, color)
        if out:
            out.append(f"{ESC}[39m")
            self.write(out)

    def _composite_get(self, overlay):
        def tg(cell):
            bm, bc = self.base.get(cell, (0, None))
            if cell in overlay:
                om, oc = overlay[cell]
                return (bm | om, oc if om else bc)
            return (bm, bc)
        return tg

    def present(self, base_touched=()):
        new_overlay = self.compute_overlay()
        cells = set(base_touched) | set(new_overlay) | self.overlay_prev
        self.blit_cells(cells, self._composite_get(new_overlay))
        self.overlay = new_overlay
        self.overlay_prev = set(new_overlay)

    def rebuild_base(self):
        new = {}
        for s in self.shapes:
            self.apply_shape(new, s)
        cells = set(new) | set(self.displayed)
        self.base = new
        self.overlay = {}
        self.overlay_prev = set()
        self.blit_cells(cells, lambda c: self.base.get(c, (0, None)))

    def ring_overlay(self, center, r):
        grid, touched = {}, set()
        for (x, y) in circle_dots(center[0], center[1], r):
            self._set(grid, x, y, CURSOR_COLOR, touched)
        return grid

    def compute_overlay(self):
        if self.tool == "select":
            return self.select_overlay()
        if self.active and self.stroke_tool not in ("free", "erase"):
            preview = {"t": self.stroke_tool, "p": [self.start, self.mouse_dot],
                       "c": list(self.color)}
            grid = {}
            self.apply_shape(grid, preview)
            return grid
        if self.tool == "erase" or (self.active and self.stroke_tool == "erase"):
            return self.ring_overlay(self.mouse_dot, self.erase_r)
        return {}

    def push_state(self, new_shapes, rebuild=False):
        self.history = self.history[:self.hidx + 1]
        self.history.append(new_shapes)
        self.hidx += 1
        self.shapes = new_shapes
        self.dirty = True
        if rebuild:
            self.rebuild_base()

    def undo(self):
        if self.hidx > 0:
            self.hidx -= 1
            self.shapes = self.history[self.hidx]
            self.rebuild_base()
        self.status()
        self.present()

    def redo(self):
        if self.hidx < len(self.history) - 1:
            self.hidx += 1
            self.shapes = self.history[self.hidx]
            self.rebuild_base()
        self.status()
        self.present()

    def on_press(self, dx, dy, button):
        tool = "erase" if button == 2 else self.tool
        self.active = True
        self.stroke_tool = tool
        self.start = (dx, dy)
        if tool in ("free", "erase"):
            self.cur_pts = [(dx, dy)]
            return self.free_segment((dx, dy), (dx, dy), tool == "erase")
        return set()

    def on_drag(self, dx, dy):
        if self.stroke_tool in ("free", "erase"):
            last = self.cur_pts[-1]
            self.cur_pts.append((dx, dy))
            return self.free_segment(last, (dx, dy), self.stroke_tool == "erase")
        return set()

    def on_release(self, dx, dy):
        if not self.active:
            return set()
        self.active = False
        if self.stroke_tool == "erase":
            shape = {"t": "erase", "p": self.cur_pts, "c": list(self.color),
                     "r": self.erase_r}
            self.push_state(self.shapes + [shape])
            return set()
        if self.stroke_tool == "free":
            shape = {"t": "free", "p": self.cur_pts, "c": list(self.color)}
            self.push_state(self.shapes + [shape])
            return set()
        shape = {"t": self.stroke_tool, "p": [self.start, (dx, dy)],
                 "c": list(self.color)}
        touched = self.apply_shape(self.base, shape)
        self.push_state(self.shapes + [shape])
        return touched

    def free_segment(self, a, b, erase):
        touched = set()
        if erase:
            self._erase_path(self.base, [a, b], self.erase_r, touched)
        else:
            for (x, y) in line_dots(*a, *b):
                self._set(self.base, x, y, self.color, touched)
        return touched

    def handle_canvas_mouse(self, b, x, y, final):
        if self.tool == "select":
            self.handle_select_mouse(b, x, y, final)
            return
        dx, dy = self.to_dot(x, y)
        self.mouse_dot = (dx, dy)
        if b & 64:                             # scroll wheel (64 up / 65 down)
            self.on_wheel(up=(b & 1) == 0)
            return
        if final == "m":
            touched = self.on_release(dx, dy)
        elif not (b & 32):
            touched = self.on_press(dx, dy, b & 3)
        elif self.active:
            touched = self.on_drag(dx, dy)
        else:
            touched = set()
        self.present(touched)

    def on_wheel(self, up):
        if self.tool == "erase" or (self.active and self.stroke_tool == "erase"):
            if up:
                self.erase_r = min(MAX_ERASE_R, self.erase_r + 1)
            else:
                self.erase_r = max(MIN_ERASE_R, self.erase_r - 1)
            self.status()
            self.present()

    # ---- select tool (marquee-select shapes, then move them) ----
    def _clear_selection(self):
        self.sel_indices = set()
        self.sel_mode = None
        self.sel_bbox = None
        self.move_base = None

    def _translate_shape(self, shape, delta):
        ns = {k: v for k, v in shape.items() if k != "_prev"}
        ns["p"] = [(x + delta[0], y + delta[1]) for (x, y) in shape["p"]]
        return ns

    def _shape_bbox(self, shape):
        # cheap point-based bbox; erase strokes are not selectable objects
        if shape["t"] == "erase" or not shape["p"]:
            return None
        xs = [p[0] for p in shape["p"]]
        ys = [p[1] for p in shape["p"]]
        return (min(xs), min(ys), max(xs), max(ys))

    def _shapes_in_rect(self, a, b):
        rx0, rx1 = sorted((a[0], b[0]))
        ry0, ry1 = sorted((a[1], b[1]))
        hits = set()
        for i, sh in enumerate(self.shapes):
            bb = self._shape_bbox(sh)
            if not bb:
                continue
            x0, y0, x1, y1 = bb
            if x0 <= rx1 and x1 >= rx0 and y0 <= ry1 and y1 >= ry0:
                hits.add(i)
        return hits

    def _update_sel_bbox(self):
        boxes = [self._shape_bbox(self.shapes[i]) for i in self.sel_indices
                 if 0 <= i < len(self.shapes)]
        boxes = [bb for bb in boxes if bb]
        if not boxes:
            self.sel_bbox = None
            return
        self.sel_bbox = (min(bb[0] for bb in boxes), min(bb[1] for bb in boxes),
                         max(bb[2] for bb in boxes), max(bb[3] for bb in boxes))

    def _point_in_selection(self, dx, dy):
        if not self.sel_bbox:
            return False
        x0, y0, x1, y1 = self.sel_bbox
        return x0 <= dx <= x1 and y0 <= dy <= y1

    def _rect_outline(self, grid, a, b):
        x0, x1 = sorted((a[0], b[0]))
        y0, y1 = sorted((a[1], b[1]))
        t = set()
        for (x, y) in line_dots(x0, y0, x1, y0):
            self._set(grid, x, y, MARQUEE_COLOR, t)
        for (x, y) in line_dots(x0, y1, x1, y1):
            self._set(grid, x, y, MARQUEE_COLOR, t)
        for (x, y) in line_dots(x0, y0, x0, y1):
            self._set(grid, x, y, MARQUEE_COLOR, t)
        for (x, y) in line_dots(x1, y0, x1, y1):
            self._set(grid, x, y, MARQUEE_COLOR, t)

    def _draw_shape_hl(self, grid, shape, color):
        if shape["t"] == "erase":
            return
        self.apply_shape(grid, {**shape, "c": list(color)})

    def select_overlay(self):
        ov = {}
        if self.active and self.sel_mode == "marquee":
            for i in self._shapes_in_rect(self.sel_start, self.sel_last):
                self._draw_shape_hl(ov, self.shapes[i], SELECT_HL)
            self._rect_outline(ov, self.sel_start, self.sel_last)
            return ov
        if self.active and self.sel_mode == "move":
            delta = (self.sel_last[0] - self.sel_start[0],
                     self.sel_last[1] - self.sel_start[1])
            for i in self.sel_indices:
                if 0 <= i < len(self.shapes):
                    self.apply_shape(
                        ov, self._translate_shape(self.shapes[i], delta))
            return ov
        for i in self.sel_indices:                  # idle: highlight selection
            if 0 <= i < len(self.shapes):
                self._draw_shape_hl(ov, self.shapes[i], SELECT_HL)
        return ov

    def handle_select_mouse(self, b, x, y, final):
        if b & 64:
            return
        dx, dy = self.to_dot(x, y)
        self.mouse_dot = (dx, dy)
        if final == "m":
            self.select_release(dx, dy)
        elif not (b & 32):
            self.select_press(dx, dy, b & 3)
        elif self.active:
            self.select_last_drag(dx, dy)

    def select_press(self, dx, dy, button):
        if button == 2:                             # right-click clears selection
            self._clear_selection()
            self.present()
            self.status()
            return
        if self.sel_indices and self._point_in_selection(dx, dy):
            self.active = True
            self.sel_mode = "move"
            self.sel_start = (dx, dy)
            self.sel_last = (dx, dy)
            self.move_base = {}                     # static base of non-selected shapes
            for i, sh in enumerate(self.shapes):
                if i not in self.sel_indices:
                    self.apply_shape(self.move_base, sh)
            self.base = self.move_base
        else:
            self.active = True
            self.sel_mode = "marquee"
            self.sel_start = (dx, dy)
            self.sel_last = (dx, dy)
            self.sel_indices = set()
            self.sel_bbox = None
        self.present()

    def select_last_drag(self, dx, dy):
        self.sel_last = (dx, dy)
        self.present()

    def select_release(self, dx, dy):
        if not self.active:
            return
        self.active = False
        if self.sel_mode == "marquee":
            self.sel_indices = self._shapes_in_rect(self.sel_start, (dx, dy))
            self._update_sel_bbox()
            self.sel_mode = None
            self.flash = (f"{len(self.sel_indices)} selected" if self.sel_indices
                          else "nothing selected")
            self.status()
            self.present()
        elif self.sel_mode == "move":
            delta = (dx - self.sel_start[0], dy - self.sel_start[1])
            self.sel_mode = None
            self.move_base = None
            if delta != (0, 0) and self.sel_indices:
                new_shapes = [self._translate_shape(s, delta) if i in self.sel_indices
                              else s for i, s in enumerate(self.shapes)]
                self.push_state(new_shapes)
            self.rebuild_base()
            self._update_sel_bbox()
            self.present()

    def handle_canvas_key(self, ch):
        act = self.ckeys.get(ch)
        if act:
            self.run_canvas_action(act)
        elif ch in ("\t", "q", "\x03"):       # always-on: back to board
            self.collapse_to_board()
        elif ch in "12345678":
            name, col = PALETTE[int(ch) - 1]
            self.color, self.color_name = col, name
            self.status()
        elif ch == "]":
            self.erase_r = min(MAX_ERASE_R, self.erase_r + 1)
            self.status()
            self.present()
        elif ch == "[":
            self.erase_r = max(MIN_ERASE_R, self.erase_r - 1)
            self.status()
            self.present()
        elif ch == "?":
            self.open_help()

    def run_canvas_action(self, act):
        if act in TOOL_ACTIONS:
            self._clear_selection()
            self.tool = act
            self.flash = ""
            self.status()
            self.present()
        elif act == "select":
            self.tool = "select"
            self.flash = "select: drag a box, then drag it to move"
            self.status()
            self.present()
        elif act == "undo":
            self._clear_selection()
            self.undo()
        elif act == "redo":
            self._clear_selection()
            self.redo()
        elif act == "clear":
            self.push_state([], rebuild=True)
            self.status()
            self.present()
        elif act == "export":
            self.begin_prompt("export")
        elif act == "back":
            self.collapse_to_board()

    # ============================ BOARD ====================================
    def node_by_id(self, nid):
        for n in self.nodes:
            if n["id"] == nid:
                return n
        return None

    def node_at(self, col, row):
        for n in reversed(self.nodes):
            if n["bx"] <= col < n["bx"] + n["w"] and n["by"] <= row < n["by"] + n["h"]:
                return n
        return None

    def node_center(self, n):
        return (n["bx"] + n["w"] // 2, n["by"] + n["h"] // 2)

    def tab_span(self, n):
        """Cells of the open-tab on a node's top border: (row, col0, col1)."""
        row = n["by"]
        col1 = n["bx"] + n["w"] - 2          # one cell left of the ┐ corner
        col0 = col1 - (len(TAB_LABEL) - 1)
        return row, col0, col1

    def tab_at(self, col, row):
        for n in reversed(self.nodes):
            r, c0, c1 = self.tab_span(n)
            if row == r and c0 <= col <= c1:
                return n
        return None

    def in_any_box(self, col, row):
        return self.node_at(col, row) is not None

    def new_node(self, col, row):
        nid = self.next_id
        self.next_id += 1
        bx = max(1, min(self.cols - NODE_W + 1, col - NODE_W // 2))
        by = max(1, min(self.status_row - NODE_H, row - NODE_H // 2))
        shapes = []
        node = {"id": nid, "title": f"canvas {nid}", "bx": bx, "by": by,
                "w": NODE_W, "h": NODE_H, "shapes": shapes,
                "hist": [shapes], "hidx": 0, "_prev": None}
        self.nodes.append(node)
        self.selected = nid
        self.dirty = True
        self.flash = f"created {node['title']}"
        self.render_board()
        self.status()

    def new_board(self):
        self.nodes = []
        self.edges = []
        self.next_id = 1
        self.selected = None
        self.link_from = None
        self.dragging = None
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.new_node(self.cols // 2, self.rows // 2)
        self.dirty = True
        self.flash = "new board"
        self.status()

    def copy_node(self, nid):
        src = self.node_by_id(nid)
        if not src:
            return
        # independent deep copy
        shapes = json.loads(json.dumps(src["shapes"]))
        new_id = self.next_id
        self.next_id += 1
        bx = max(1, min(self.cols - src["w"] + 1, src["bx"] + 2))
        by = max(1, min(self.status_row - src["h"], src["by"] + 1))
        node = {"id": new_id, "title": src["title"] + " copy",
                "bx": bx, "by": by, "w": src["w"], "h": src["h"],
                "shapes": shapes, "hist": [shapes], "hidx": 0, "_prev": None}
        self.nodes.append(node)
        self.selected = new_id
        self.dirty = True
        self.flash = "copied node"
        self.render_board()
        self.status()

    def delete_node(self, nid):
        self.nodes = [n for n in self.nodes if n["id"] != nid]
        self.edges = [e for e in self.edges if nid not in e]
        if self.selected == nid:
            self.selected = self.nodes[-1]["id"] if self.nodes else None
        self.dirty = True
        self.flash = "deleted node"
        self.render_board()
        self.status()

    def toggle_edge(self, a, b):
        self.dirty = True
        key = sorted((a, b))
        for i, e in enumerate(self.edges):
            if sorted(e) == key:
                self.edges.pop(i)
                return
        self.edges.append(key)

    def open_node(self, n):
        self.active_node = n["id"]
        self.shapes = n["shapes"]
        self.history = n["hist"]
        self.hidx = n["hidx"]
        self._clear_selection()
        self.mode = "canvas"
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.rebuild_base()
        self.status()
        self.present()

    def collapse_to_board(self):
        n = self.node_by_id(self.active_node)
        if n:
            n["shapes"] = self.shapes
            n["hist"] = self.history
            n["hidx"] = self.hidx
            n["_prev"] = None              # invalidate cached preview
            self.selected = n["id"]
        self.active = False
        if self.canvas:                     # canvas-draw mode has no board to return to
            self.running = False
            return
        self.active_node = None
        self.mode = "board"
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.render_board()
        self.status()

    # ---- board rendering ----
    def _scale_shape(self, sh, s, ox, oy):
        ns = {"t": sh["t"], "c": sh["c"],
              "p": [(x * s + ox, y * s + oy) for (x, y) in sh["p"]]}
        if "r" in sh:
            ns["r"] = max(1, int(round(sh["r"] * s)))
        return ns

    def preview_block(self, n):
        inner, ih = n["w"] - 2, n["h"] - 2
        if n["_prev"] is not None:
            return n["_prev"]
        if not n["shapes"]:
            n["_prev"] = [" " * inner for _ in range(ih)]
            return n["_prev"]
        pdw, pdh = inner * 2, ih * 4
        s = min(pdw / self.dw, pdh / self.dh)
        ox = (pdw - self.dw * s) / 2
        oy = (pdh - self.dh * s) / 2
        sdw, sdh = self.dw, self.dh
        self.dw, self.dh = pdw, pdh
        grid = {}
        try:
            for sh in n["shapes"]:
                self.apply_shape(grid, self._scale_shape(sh, s, ox, oy))
        finally:
            self.dw, self.dh = sdw, sdh
        rows = []
        for ry in range(ih):
            line = []
            for rx in range(inner):
                m = grid.get((rx, ry), (0, None))[0]
                line.append(chr(BRAILLE_BASE + m) if m else " ")
            rows.append("".join(line))
        n["_prev"] = rows
        return rows

    def draw_node_into(self, target, n):
        linking = self.link_from is not None
        recolor_sel = self.cfg.get("hover_recolor_selected", False)
        accent = NODE_COLOR
        if n["id"] == self.hover and (recolor_sel or n["id"] != self.selected):
            accent = SEL_COLOR if linking else HOVER_COLOR
        if n["id"] == self.selected and not (linking and n["id"] == self.hover):
            accent = SEL_COLOR
        if n["id"] == self.link_from:
            accent = LINK_COLOR
        x0, y0, w, h = n["bx"], n["by"], n["w"], n["h"]
        inner = w - 2
        label = (" " + n["title"] + " ")[:inner]
        top = BOX_TL + label + BOX_H * (inner - len(label)) + BOX_TR
        bottom = BOX_BL + BOX_H * inner + BOX_BR
        for i, ch in enumerate(top):
            target[(y0, x0 + i)] = (ch, accent)
        for i, ch in enumerate(bottom):
            target[(y0 + h - 1, x0 + i)] = (ch, accent)
        trow, tc0, _ = self.tab_span(n)
        tcolor = TAB_HOVER if n["id"] == self.hover_tab else TAB_COLOR
        for i, ch in enumerate(TAB_LABEL):
            target[(trow, tc0 + i)] = (ch, tcolor)
        for ry in range(1, h - 1):
            target[(y0 + ry, x0)] = (BOX_V, accent)
            target[(y0 + ry, x0 + w - 1)] = (BOX_V, accent)
        rows = self.preview_block(n)
        for ry, line in enumerate(rows):
            for rx, ch in enumerate(line):
                target[(y0 + 1 + ry, x0 + 1 + rx)] = (ch, PREVIEW_COLOR)

    def render_board(self):
        target = {}
        for a, b in self.edges:
            na, nb = self.node_by_id(a), self.node_by_id(b)
            if not na or not nb:
                continue
            ca, cb = self.node_center(na), self.node_center(nb)
            for (col, row) in line_dots(ca[0], ca[1], cb[0], cb[1]):
                if 1 <= row < self.status_row and 1 <= col <= self.cols \
                        and not self.in_any_box(col, row):
                    target[(row, col)] = ("·", EDGE_COLOR)
        for n in self.nodes:
            self.draw_node_into(target, n)
        if not self.nodes:
            hint = "empty board — press  n  to create a node"
            row = self.rows // 2
            col = max(1, (self.cols - len(hint)) // 2)
            for i, ch in enumerate(hint):
                target[(row, col + i)] = (ch, NODE_COLOR)
        if self.menu is not None:
            self._draw_menu_into(target)
        self.draw_text_target(target)

    def draw_text_target(self, target):
        out = []
        for cell in set(target) | set(self.txt):
            row, col = cell
            t = target.get(cell)
            cur = self.txt.get(cell)
            if t is None:
                if cur is not None:
                    out.append(f"{ESC}[{row};{col}H ")
                    self.txt.pop(cell, None)
            elif t != cur:
                ch, fg = t
                if fg:
                    out.append(
                        f"{ESC}[{row};{col}H{ESC}[38;2;{fg[0]};{fg[1]};{fg[2]}m{ch}")
                else:
                    out.append(f"{ESC}[{row};{col}H{ch}")
                self.txt[cell] = t
        if out:
            out.append(f"{ESC}[39m")
            self.write(out)

    # ---- board input ----
    def handle_board_mouse(self, b, x, y, final):
        if self.menu is not None:
            self.handle_menu_mouse(b, x, y, final)
            return
        if b & 64:
            return
        col, row = self.to_cell(x, y)
        self.mouse_cell = (col, row)
        hovered = self.node_at(col, row)
        hid = hovered["id"] if hovered else None
        tab = self.tab_at(col, row)
        tid = tab["id"] if tab else None
        changed = (hid != self.hover) or (tid != self.hover_tab)
        self.hover = hid
        self.hover_tab = tid
        if final == "m":
            self.dragging = None
            if changed:
                self.render_board()
            return
        if not (b & 32):
            if (b & 3) == 2:
                self.open_menu(col, row)     # right-click -> context menu
            elif tab is not None:
                self.tab_press(tab)          # double-click the tab to open
            else:
                self.board_press(col, row, b & 3)
        elif self.dragging:
            self.board_drag(col, row)
        elif changed:
            self.render_board()       # plain hover motion

    def board_press(self, col, row, button):
        node = self.node_at(col, row)
        if self.link_from is not None:
            if node and node["id"] != self.link_from:
                self.toggle_edge(self.link_from, node["id"])
                self.flash = "linked"
            else:
                self.flash = "link cancelled"
            # selection stays on the node that initiated the link
            self.link_from = None
            self.render_board()
            self.status()
            return
        if node:
            self.selected = node["id"]
            self.dragging = (node, col - node["bx"], row - node["by"])
            self.press_cell = (col, row)
            self.press_moved = False
            self.render_board()
            self.status()
        else:
            self.selected = None
            self.dragging = None
            self.render_board()
            self.status()

    def tab_press(self, node):
        """A press on a node's open-tab; the second within DOUBLE_CLICK_S opens it."""
        nid = node["id"]
        now = time.monotonic()
        last_id, last_t = self.last_tab_click
        self.selected = nid
        self.dragging = None          # grabbing the tab never starts a drag
        if last_id == nid and (now - last_t) <= DOUBLE_CLICK_S:
            self.last_tab_click = (None, 0.0)
            self.open_node(node)
            return
        self.last_tab_click = (nid, now)
        self.flash = "double-click the tab to open"
        self.render_board()
        self.status()

    def board_drag(self, col, row):
        node, offc, offr = self.dragging
        if (col, row) != self.press_cell:
            self.press_moved = True
            self.dirty = True
        node["bx"] = max(1, min(self.cols - node["w"] + 1, col - offc))
        node["by"] = max(1, min(self.status_row - node["h"], row - offr))
        self.render_board()

    # ---- right-click context menu ----
    def open_menu(self, col, row):
        node = self.node_at(col, row)
        if node:
            self.selected = node["id"]
            items = [("Enter", "enter"), ("Rename", "rename"),
                     ("Copy", "copy"), ("Link", "link"), ("Delete", "delete")]
            target = node["id"]
        else:
            items = [("New node", "new_node"), ("New board", "new_board")]
            target = None
        inner = max(len(l) for l, _ in items) + 4
        w, h = inner + 2, len(items) + 2
        x = col if col + w - 1 <= self.cols else self.cols - w + 1
        bottom = self.status_row - 1
        y = row if row + h - 1 <= bottom else bottom - h + 1
        self.menu = {"items": items, "x": max(1, x), "y": max(1, y),
                     "w": w, "h": h, "target": target, "hover": 0, "at": (col, row)}
        self.render_board()
        self.status()

    def _draw_menu_into(self, target):
        m = self.menu
        x, y, w, h = m["x"], m["y"], m["w"], m["h"]
        inner = w - 2
        for i, ch in enumerate(BOX_TL + BOX_H * inner + BOX_TR):
            target[(y, x + i)] = (ch, MENU_BORDER)
        for i, ch in enumerate(BOX_BL + BOX_H * inner + BOX_BR):
            target[(y + h - 1, x + i)] = (ch, MENU_BORDER)
        for r, (label, _) in enumerate(m["items"]):
            ry = y + 1 + r
            target[(ry, x)] = (BOX_V, MENU_BORDER)
            target[(ry, x + w - 1)] = (BOX_V, MENU_BORDER)
            marker = "▸" if r == m["hover"] else " "
            text = f"{marker} {label}".ljust(inner)
            color = SEL_COLOR if r == m["hover"] else MENU_TEXT
            for c, ch in enumerate(text):
                target[(ry, x + 1 + c)] = (ch, color)

    def handle_menu_mouse(self, b, x, y, final):
        if b & 64:
            return
        col, row = self.to_cell(x, y)
        m = self.menu
        inside = m["x"] <= col < m["x"] + \
            m["w"] and m["y"] <= row < m["y"] + m["h"]
        on_item = inside and m["y"] < row < m["y"] + m["h"] - 1
        idx = (row - m["y"] - 1) if on_item else None
        if final == "m":                       # click / release
            if idx is not None:
                self.run_menu(idx)
            elif not inside:
                self.close_menu()
            return
        if not (b & 32):                       # press outside -> dismiss
            if not inside:
                self.close_menu()
            return
        if idx is not None and idx != m["hover"]:   # hover within the menu
            m["hover"] = idx
            self.render_board()

    def run_menu(self, idx):
        m = self.menu
        if not m or not (0 <= idx < len(m["items"])):
            self.close_menu()
            return
        action = m["items"][idx][1]
        target = m["target"]
        at = m["at"]
        self.menu = None
        self.render_board()
        self.status()
        if action == "enter":
            n = self.node_by_id(target)
            if n:
                self.open_node(n)
        elif action == "rename":
            if target is not None:
                self.selected = target
                self.begin_prompt("rename")
        elif action == "delete":
            if target is not None:
                self.delete_node(target)
        elif action == "copy":
            if target is not None:
                self.copy_node(target)
        elif action == "link":
            if target is not None:
                self.selected = target
                self.link_from = target
                self.flash = "click a node to link"
                self.render_board()
                self.status()
        elif action == "new_node":
            self.new_node(*at)
        elif action == "new_board":
            self.new_board()

    def close_menu(self):
        self.menu = None
        self.render_board()
        self.status()

    # ============================ SETTINGS =================================
    def toggle_ui(self):
        self.cfg["hide_ui"] = not self.cfg.get("hide_ui")
        self.save_config()
        self.status()

    # ---- quit / save confirmation ----
    def ask_confirm(self, msg, options, kind, data=None):
        self.confirm = {"msg": msg, "options": options,
                        "kind": kind, "data": data}
        self.status()

    def _sync_active_node(self):
        if self.active_node is not None:
            n = self.node_by_id(self.active_node)
            if n:
                n["shapes"] = self.shapes
                n["hist"] = self.history
                n["hidx"] = self.hidx
                n["_prev"] = None

    def request_quit(self):
        self._sync_active_node()
        if self.dirty:
            self.ask_confirm("Unsaved changes.",
                             [("s", "save & quit"), ("q", "quit anyway"),
                              ("c", "cancel")], kind="quit")
        else:
            self.running = False

    def try_save_board(self, name):
        path = self._resolve(self._with_ext(name, ".json"), "save")
        if os.path.exists(path):
            self.ask_confirm(f"{os.path.basename(path)} exists — overwrite?",
                             [("y", "overwrite"), ("r", "new name"),
                              ("c", "cancel")],
                             kind="overwrite", data=name)
        else:
            self.do_save_board(name)

    def resolve_confirm(self, kind, key, data):
        if kind == "quit":
            if key == "s":
                self.quit_after_save = True
                self.begin_prompt("save_board")
            elif key == "q":
                self.running = False
            else:
                self.status()
        elif kind == "switch_board":
            if key == "o":
                self.do_load_board_path(data)
            else:
                self.flash = "cancelled"
                self.render_boards()
                self.status()
        elif kind == "overwrite":
            if key == "y":
                self.do_save_board(data)
            elif key == "r":
                self.begin_prompt("save_board")
                self.prompt_buf = data       # prefill the attempted name to edit
                self.status()
            else:
                self.quit_after_save = False
                self.flash = "save cancelled"
                self.status()

    def build_settings_rows(self):
        rows = [
            {"type": "header", "label": "Features"},
            {"type": "toggle", "label": "Hover recolors selected node",
             "key": "hover_recolor_selected"},
            {"type": "toggle", "label": "Show hint labels in status bar",
             "key": "show_hint_labels"},
            {"type": "toggle", "label": "Hide UI / status bar", "key": "hide_ui"},
            {"type": "header", "label": "Defaults"},
            {"type": "choice", "label": "Default tool", "key": "default_tool",
             "opts": list(TOOL_ACTIONS)},
            {"type": "choice", "label": "Default color", "key": "default_color",
             "opts": list(range(len(PALETTE)))},
            {"type": "int", "label": "Default eraser size", "key": "default_erase"},
            {"type": "header", "label": "Paths"},
            {"type": "path", "label": "Working directory", "key": "work_dir"},
            {"type": "path", "label": "Save directory", "key": "save_dir"},
            {"type": "path", "label": "Open directory", "key": "open_dir"},
            {"type": "header", "label": "Startup"},
            {"type": "toggle", "label": "Auto-open a board on launch",
             "key": "autoload"},
            {"type": "path", "label": "Auto-open file name", "key": "autoload_file"},
            {"type": "path", "label": "Auto-open directory", "key": "autoload_dir"},
            {"type": "info", "label": "Settings file",
             "value": self._tilde(self.config_path)},
            {"type": "header", "label": "Keymap — board"},
        ]
        for a, label, _ in BOARD_BIND:
            rows.append({"type": "key", "label": label, "key": "board." + a})
        rows.append({"type": "header", "label": "Keymap — canvas"})
        for a, label, _ in CANVAS_BIND:
            rows.append({"type": "key", "label": label, "key": "canvas." + a})
        rows.append({"type": "header", "label": ""})
        rows.append(
            {"type": "action", "label": "Reset to defaults", "key": "reset"})
        rows.append(
            {"type": "action", "label": "Save & close", "key": "close"})
        return rows

    def _setting_value(self, row):
        t, key = row["type"], row.get("key")
        if t == "toggle":
            return "[x] on" if self.cfg.get(key) else "[ ] off"
        if t == "choice":
            v = self.cfg.get(key)
            if key == "default_color":
                return PALETTE[v % len(PALETTE)][0]
            return str(v)
        if t == "int":
            return str(self.cfg.get(key))
        if t == "path":
            return self.cfg.get(key) or "(default)"
        if t == "info":
            return row.get("value", "")
        if t == "key":
            return self._keyname(self.cfg["keymap"].get(key, "?"))
        return ""

    def _apply_live(self, key):
        if key == "default_tool":
            self.tool = self.cfg["default_tool"]
        elif key == "default_color":
            ci = self.cfg["default_color"] % len(PALETTE)
            self.color_name, self.color = PALETTE[ci]
        elif key == "default_erase":
            self.erase_r = self.cfg["default_erase"]

    def _settings_view_h(self):
        return max(1, self.status_row - 3)

    def _selectable_row(self, row):
        return row["type"] not in ("header", "info")

    def _ensure_hover_visible(self):
        view_h = self._settings_view_h()
        if self.settings_hover < self.settings_top:
            self.settings_top = self.settings_hover
        elif self.settings_hover >= self.settings_top + view_h:
            self.settings_top = self.settings_hover - view_h + 1

    def open_settings(self):
        self.mode = "settings"
        self.settings_rows = self.build_settings_rows()
        self.settings_top = 0
        self.settings_hover = next((i for i, r in enumerate(self.settings_rows)
                                    if self._selectable_row(r)), 0)
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.render_settings()
        self.status()

    def close_settings(self):
        self.save_config()
        self.rebuild_keymaps()
        self.mode = "board"
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.render_board()
        self.status()

    def render_settings(self):
        target = {}
        title = "  SETTINGS  ·  saved to " + self._tilde(self.config_path)
        for i, ch in enumerate(title[:self.cols]):
            target[(1, 1 + i)] = (ch, SEL_COLOR)
        top_row = 3
        view_h = self._settings_view_h()
        rows = self.settings_rows
        # page scroll is independent of the hovered row; just keep it in range
        max_top = max(0, len(rows) - view_h)
        self.settings_top = max(0, min(self.settings_top, max_top))
        label_col = 3
        val_col = min(max(38, self.cols - 24), self.cols - 6)
        for vi in range(view_h):
            ri = self.settings_top + vi
            if ri >= len(rows):
                break
            row = rows[ri]
            sr = top_row + vi
            if row["type"] == "header":
                head = ("— " + row["label"]) if row["label"] else ""
                for i, ch in enumerate(head[:self.cols - label_col]):
                    target[(sr, label_col + i)] = (ch, NODE_COLOR)
                continue
            hovered = (ri == self.settings_hover)
            label = ("▸ " if hovered else "  ") + row["label"]
            lcolor = SEL_COLOR if hovered else MENU_TEXT
            for i, ch in enumerate(label[:val_col - label_col - 1]):
                target[(sr, label_col + i)] = (ch, lcolor)
            val = self._setting_value(row)
            vcolor = SEL_COLOR if hovered else HOVER_COLOR
            for i, ch in enumerate(val[:self.cols - val_col]):
                target[(sr, val_col + i)] = (ch, vcolor)
        self.draw_text_target(target)

    def settings_scroll(self, delta):
        rows = self.settings_rows
        step = 1 if delta > 0 else -1
        i = self.settings_hover + step
        while 0 <= i < len(rows) and not self._selectable_row(rows[i]):
            i += step
        if 0 <= i < len(rows):
            self.settings_hover = i
            self._ensure_hover_visible()
            self.render_settings()

    def settings_wheel(self, delta):
        view_h = self._settings_view_h()
        max_top = max(0, len(self.settings_rows) - view_h)
        self.settings_top = max(0, min(self.settings_top + delta, max_top))
        self.render_settings()

    def activate_setting(self, ri):
        if not (0 <= ri < len(self.settings_rows)):
            return
        row = self.settings_rows[ri]
        t, key = row["type"], row.get("key")
        if t == "toggle":
            self.cfg[key] = not self.cfg.get(key)
            self.render_settings()
            self.status()
        elif t == "choice":
            opts = row["opts"]
            cur = self.cfg.get(key)
            idx = opts.index(cur) if cur in opts else -1
            self.cfg[key] = opts[(idx + 1) % len(opts)]
            self._apply_live(key)
            self.render_settings()
            self.status()
        elif t == "int":
            self.begin_prompt("set:" + key)
        elif t == "path":
            self.begin_prompt("path:" + key)
        elif t == "key":
            self.capture_action = key
            self.status()
        elif t == "action":
            if key == "reset":
                self.cfg = default_config()
                self.rebuild_keymaps()
                self.flash = "reset to defaults"
                self.render_settings()
                self.status()
            elif key == "close":
                self.close_settings()

    def finish_capture(self, ch):
        if ch in ("\x03", "ESC"):
            self.capture_action = None
            self.flash = "cancelled"
        elif len(ch) == 1:                     # bind a single key
            self.cfg["keymap"][self.capture_action] = ch
            self.capture_action = None
            self.rebuild_keymaps()
            self.flash = f"bound to {self._keyname(ch)}"
        else:
            return                             # ignore arrow tokens, keep waiting
        self.render_settings()
        self.status()

    def handle_settings_mouse(self, b, x, y, final):
        if b & 64:
            self.settings_wheel(3 if (b & 1) else -3)
            return
        col, row = self.to_cell(x, y)
        ri = self.settings_top + (row - 3)
        valid = (0 <= ri < len(self.settings_rows)
                 and self._selectable_row(self.settings_rows[ri]))
        if final == "m":
            if valid:
                self.settings_hover = ri
                self.activate_setting(ri)
            return
        if valid and ri != self.settings_hover:
            self.settings_hover = ri
            self.render_settings()

    def handle_settings_key(self, ch):
        if ch in ("q", "\x03", "ESC"):
            self.close_settings()
        elif ch in ("\r", "\n"):
            self.activate_setting(self.settings_hover)
        elif ch in ("j", "DOWN", "\t"):
            self.settings_scroll(1)
        elif ch in ("k", "UP"):
            self.settings_scroll(-1)

    def handle_board_key(self, ch):
        act = self.bkeys.get(ch)
        if act:
            self.run_board_action(act)
        elif ch in ("q", "\x03"):             # always-on
            self.request_quit()
        elif ch in ("\r", "\n"):
            if self.selected is not None:
                n = self.node_by_id(self.selected)
                if n:
                    self.open_node(n)
        elif ch == "\t":
            if self.nodes:
                ids = [n["id"] for n in self.nodes]
                i = (ids.index(self.selected) + 1) % len(ids) \
                    if self.selected in ids else 0
                self.selected = ids[i]
                self.render_board()
                self.status()
        elif ch == "?":
            self.open_help()

    def run_board_action(self, act):
        if act == "new_node":
            self.new_node(*self.mouse_cell)
        elif act == "new_board":
            self.new_board()
        elif act == "delete":
            if self.selected is not None:
                self.delete_node(self.selected)
        elif act == "link":
            if self.link_from is not None:
                self.link_from = None
                self.flash = "link cancelled"
            elif self.selected is not None:
                self.link_from = self.selected
                self.flash = "click a node to link"
            self.render_board()
            self.status()
        elif act == "rename":
            if self.selected is not None:
                self.begin_prompt("rename")
        elif act == "save":
            self.begin_prompt("save_board")
        elif act == "open":
            self.begin_prompt("open_board")
        elif act == "boards":
            self.open_boards()
        elif act == "settings":
            self.open_settings()

    # ============================ PROMPT / FILES ===========================
    def begin_prompt(self, mode):
        self.prompt_mode = mode
        if mode == "rename":
            n = self.node_by_id(self.selected)
            self.prompt_buf = n["title"] if n else ""
        elif mode.startswith("set:"):
            self.prompt_buf = str(self.cfg.get(mode[4:], ""))
        elif mode.startswith("path:"):
            self.prompt_buf = str(self.cfg.get(mode[5:], ""))
        else:
            self.prompt_buf = self.last_name
        self.status()

    def handle_prompt_key(self, ch):
        if ch in ("\r", "\n"):
            name = self.prompt_buf.strip()
            mode = self.prompt_mode
            self.prompt_mode = None
            if mode.startswith("set:"):           # numeric setting
                k = mode[4:]
                try:
                    self.cfg[k] = max(MIN_ERASE_R, min(MAX_ERASE_R, int(name)))
                    self._apply_live(k)
                except ValueError:
                    self.flash = "invalid number"
                self.render_settings()
                self.status()
                return
            if mode.startswith("path:"):          # path setting (empty = clear)
                self.cfg[mode[5:]] = name
                self.render_settings()
                self.status()
                return
            if not name:
                self.flash = "cancelled"
                self.status()
            elif mode == "rename":
                n = self.node_by_id(self.selected)
                if n:
                    n["title"] = name
                self.dirty = True
                self.flash = "renamed"
                self.render_board()
                self.status()
            elif mode == "save_board":
                self.try_save_board(name)
            elif mode == "open_board":
                self.do_load_board(name)
            elif mode == "export":
                self.do_export(name)
        elif ch in ("\x7f", "\b"):
            self.prompt_buf = self.prompt_buf[:-1]
            self.status()
        elif ch in ("\x03", "ESC"):
            self.prompt_mode = None
            self.quit_after_save = False
            self.flash = "cancelled"
            self.status()
        elif len(ch) == 1 and ch.isprintable():    # ignore arrow tokens etc
            self.prompt_buf += ch
            self.status()

    @staticmethod
    def _with_ext(name, ext):
        return name if name.lower().endswith(ext) else name + ext

    @staticmethod
    def _stem(name):
        for ext in (".json", ".svg"):
            if name.lower().endswith(ext):
                return name[:-len(ext)]
        return name

    def do_save_board(self, name):
        self._sync_active_node()
        path = self._resolve(self._with_ext(name, ".json"), "save")
        data = {"nodes": [{k: n[k] for k in
                           ("id", "title", "bx", "by", "w", "h", "shapes")}
                          for n in self.nodes],
                "edges": self.edges, "next_id": self.next_id}
        saved = False
        try:
            with open(path, "w") as f:
                json.dump(data, f)
            self.last_name = self._stem(name)
            self._remember_board(path)
            self.flash = f"saved {path} ({len(self.nodes)} nodes)"
            saved = True
            self.dirty = False
        except Exception as e:
            self.flash = f"save failed: {e}"
        self.status()
        if saved and self.quit_after_save:
            self.quit_after_save = False
            self.running = False

    def _apply_board_data(self, data):
        self.nodes = []
        for nd in data.get("nodes", []):
            shapes = nd.get("shapes", [])
            self.nodes.append({
                "id": nd["id"], "title": nd.get("title", f"canvas {nd['id']}"),
                "bx": nd.get("bx", 2), "by": nd.get("by", 2),
                "w": nd.get("w", NODE_W), "h": nd.get("h", NODE_H),
                "shapes": shapes, "hist": [shapes], "hidx": 0, "_prev": None})
        self.edges = [list(e) for e in data.get("edges", [])]
        self.next_id = data.get("next_id",
                                max((n["id"] for n in self.nodes), default=0) + 1)
        self.selected = self.nodes[0]["id"] if self.nodes else None
        self.dirty = False

    def _autoload_path(self, stem):
        name = self._with_ext(stem, ".json")
        adir = self.cfg.get("autoload_dir")
        if adir and not os.path.isabs(os.path.expanduser(name)):
            return os.path.join(os.path.expanduser(adir), name)
        return self._resolve(name, "open")

    def autoload_board(self):
        """On startup, open a saved board if auto-open is enabled. We try the
        `autoload_file` override first, then the last board worked on, then the
        launch basename — opening the first one that exists. Paths resolve
        against `autoload_dir` (or the open/work directory)."""
        if not self.cfg.get("autoload", True):
            return
        path = None
        for stem in (self.cfg.get("autoload_file"),
                     self.cfg.get("last_board"), self.last_name):
            if not stem:
                continue
            p = self._autoload_path(stem)
            if os.path.exists(p):
                path = p
                break
        if not path:
            return
        try:
            with open(path) as f:
                data = json.load(f)
        except Exception as e:
            self.flash = f"open failed: {e}"
            return
        self._apply_board_data(data)
        self.last_name = self._stem(os.path.basename(path))
        self._remember_board(path)
        self.flash = f"opened {path} ({len(self.nodes)} nodes)"

    def do_load_board(self, name):
        self.do_load_board_path(self._resolve(self._with_ext(name, ".json"),
                                              "open"))

    def do_load_board_path(self, path):
        try:
            with open(path) as f:
                data = json.load(f)
            self._apply_board_data(data)
            self.last_name = self._stem(os.path.basename(path))
            self._remember_board(path)
            self.flash = f"opened {path} ({len(self.nodes)} nodes)"
        except Exception as e:
            self.flash = f"open failed: {e}"
        self.mode = "board"
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.render_board()
        self.status()

    # ============================ BOARD BROWSER ============================
    def _boards_dir(self):
        base = self.cfg.get("open_dir") or self.cfg.get("work_dir") or "."
        return os.path.expanduser(base)

    def _list_board_files(self):
        d = self._boards_dir()
        try:
            names = sorted(os.listdir(d))
        except OSError:
            names = []
        cfgpath = os.path.abspath(self.config_path)
        items = []
        for nm in names:
            if not nm.endswith(".json"):
                continue
            path = os.path.join(d, nm)
            if os.path.abspath(path) == cfgpath:   # skip the settings file
                continue
            try:
                with open(path) as f:
                    data = json.load(f)
                if not isinstance(data, dict) or "nodes" not in data:
                    continue                       # not a board file
                count = len(data.get("nodes", []))
            except Exception:
                continue
            items.append(
                {"name": self._stem(nm), "path": path, "count": count})
        return items

    def open_boards(self):
        self._sync_active_node()
        self.mode = "boards"
        self.board_list = self._list_board_files()
        self.board_top = 0
        self.board_hover = next((i for i, b in enumerate(self.board_list)
                                 if b["name"] == self.last_name), 0)
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.render_boards()
        self.status()

    def close_boards(self):
        self.mode = "board"
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        self.render_board()
        self.status()

    def render_boards(self):
        target = {}
        title = "  BOARDS  ·  " + self._tilde(self._boards_dir())
        for i, ch in enumerate(title[:self.cols]):
            target[(1, 1 + i)] = (ch, SEL_COLOR)
        top_row = 3
        view_h = max(1, self.status_row - top_row)
        rows = self.board_list
        if not rows:
            msg = "  no boards here — press n to start a new one"
            for i, ch in enumerate(msg[:self.cols]):
                target[(top_row, 3 + i)] = (ch, NODE_COLOR)
            self.draw_text_target(target)
            return
        max_top = max(0, len(rows) - view_h)
        self.board_top = max(0, min(self.board_top, max_top))
        label_col = 3
        val_col = min(max(38, self.cols - 16), self.cols - 2)
        for vi in range(view_h):
            ri = self.board_top + vi
            if ri >= len(rows):
                break
            b = rows[ri]
            sr = top_row + vi
            hovered = (ri == self.board_hover)
            current = (b["name"] == self.last_name)
            mark = "▸ " if hovered else ("● " if current else "  ")
            label = mark + b["name"] + ("  (current)" if current else "")
            lcolor = SEL_COLOR if hovered else (LINK_COLOR if current
                                                else MENU_TEXT)
            for i, ch in enumerate(label[:val_col - label_col - 1]):
                target[(sr, label_col + i)] = (ch, lcolor)
            cnt = f"{b['count']} node(s)" if b["count"] is not None else ""
            vcolor = SEL_COLOR if hovered else HOVER_COLOR
            for i, ch in enumerate(cnt[:self.cols - val_col]):
                target[(sr, val_col + i)] = (ch, vcolor)
        self.draw_text_target(target)

    def boards_scroll(self, delta):
        rows = self.board_list
        if not rows:
            return
        self.board_hover = max(0, min(self.board_hover + (1 if delta > 0 else -1),
                                      len(rows) - 1))
        view_h = max(1, self.status_row - 3)
        if self.board_hover < self.board_top:
            self.board_top = self.board_hover
        elif self.board_hover >= self.board_top + view_h:
            self.board_top = self.board_hover - view_h + 1
        self.render_boards()

    def boards_wheel(self, delta):
        view_h = max(1, self.status_row - 3)
        max_top = max(0, len(self.board_list) - view_h)
        self.board_top = max(0, min(self.board_top + delta, max_top))
        self.render_boards()

    def boards_open_selected(self):
        if not self.board_list:
            return
        b = self.board_list[self.board_hover]
        if b["name"] == self.last_name and not self.dirty:
            self.close_boards()                # already on this board
            return
        if self.dirty:
            self.ask_confirm("Unsaved changes will be lost.",
                             [("o", "open anyway"), ("c", "cancel")],
                             kind="switch_board", data=b["path"])
            return
        self.do_load_board_path(b["path"])

    def handle_boards_key(self, ch):
        if ch in ("q", "\x03", "ESC"):
            self.close_boards()
        elif ch in ("\r", "\n"):
            self.boards_open_selected()
        elif ch in ("j", "DOWN", "\t"):
            self.boards_scroll(1)
        elif ch in ("k", "UP"):
            self.boards_scroll(-1)
        elif ch == "n":
            self.mode = "board"
            self.new_board()

    def handle_boards_mouse(self, b, x, y, final):
        if b & 64:
            self.boards_wheel(3 if (b & 1) else -3)
            return
        if not self.board_list:
            return
        col, row = self.to_cell(x, y)
        ri = self.board_top + (row - 3)
        valid = 0 <= ri < len(self.board_list)
        if final == "m":
            if valid:
                self.board_hover = ri
                self.boards_open_selected()
            return
        if valid and ri != self.board_hover:
            self.board_hover = ri
            self.render_boards()

    def do_export(self, name):
        path = self._resolve(self._with_ext(name, ".svg"), "save")
        out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.dw}" '
               f'height="{self.dh}" viewBox="0 0 {self.dw} {self.dh}" '
               f'style="background:#1e1e1e">',
               '<g fill="none" stroke-width="1.6" stroke-linecap="round" '
               'stroke-linejoin="round">']
        for s in self.shapes:
            col = rgbhex(s["c"])
            t, p = s["t"], s["p"]
            if t == "free":
                pts = " ".join(f"{x:.0f},{y:.0f}" for x, y in p)
                out.append(f'<polyline points="{pts}" stroke="{col}"/>')
            elif t in ("line", "arrow"):
                out.append(f'<line x1="{p[0][0]:.0f}" y1="{p[0][1]:.0f}" '
                           f'x2="{p[1][0]:.0f}" y2="{p[1][1]:.0f}" stroke="{col}"/>')
                if t == "arrow":
                    for a, b in self.arrow_head(p[0], p[1]):
                        out.append(f'<line x1="{a[0]:.0f}" y1="{a[1]:.0f}" '
                                   f'x2="{b[0]:.0f}" y2="{b[1]:.0f}" stroke="{col}"/>')
            elif t == "rect":
                x0, x1 = sorted((p[0][0], p[1][0]))
                y0, y1 = sorted((p[0][1], p[1][1]))
                out.append(f'<rect x="{x0:.0f}" y="{y0:.0f}" width="{x1 - x0:.0f}" '
                           f'height="{y1 - y0:.0f}" stroke="{col}"/>')
            elif t == "ellipse":
                cx, cy = (p[0][0] + p[1][0]) / 2, (p[0][1] + p[1][1]) / 2
                rx, ry = abs(p[1][0] - p[0][0]) / 2, abs(p[1][1] - p[0][1]) / 2
                out.append(f'<ellipse cx="{cx:.0f}" cy="{cy:.0f}" rx="{rx:.0f}" '
                           f'ry="{ry:.0f}" stroke="{col}"/>')
        out.append("</g></svg>")
        try:
            with open(path, "w") as f:
                f.write("\n".join(out))
            self.last_name = self._stem(name)
            self.flash = f"exported {path}"
        except Exception as e:
            self.flash = f"export failed: {e}"
        self.status()

    # ============================ CHROME ===================================
    def bar(self, text, bg, fg=BAR_FG):
        text = text[:self.cols].ljust(self.cols)
        return f"{ESC}[{self.status_row};1H{ESC}[48;5;{bg}m{ESC}[38;5;{fg}m{text}{ESC}[0m"

    def _keyname(self, k):
        return {"\r": "Enter", "\n": "Enter", "\t": "Tab", " ": "Spc"}.get(k, k)

    def _hints(self, pairs):
        """Build a hint string from (key, label) pairs, honoring show_hint_labels"""
        show = self.cfg.get("show_hint_labels", True)
        out = []
        for key, label in pairs:
            if key is None:               # mouse-only hints: drop when labels off
                if show:
                    out.append(label)
            else:
                kn = self._keyname(key)
                out.append(f"{kn} {label}" if show else kn)
        return "| " + "  ".join(out) + " "

    def status(self):
        if self.confirm is not None:
            opts = "   ".join(f"[{k}] {lbl}" for k,
                              lbl in self.confirm["options"])
            text = f" {self.confirm['msg']}    {opts} "
            self.write([self.bar(text[:self.cols], PROMPT_BG)])
            return
        if self.prompt_mode:
            pm = self.prompt_mode
            if pm.startswith("set:"):
                label = "set " + pm[4:]
            elif pm.startswith("path:"):
                label = "set " + pm[5:].replace("_", " ")
            else:
                label = {"rename": "rename node", "save_board": "save board as",
                         "open_board": "open board", "export": "export svg"}.get(pm, pm)
            text = (f" {label}: {self.prompt_buf}█"
                    f"   [Enter] ok   [Ctrl-C] cancel ")
            self.write([self.bar(text, PROMPT_BG)])
            return
        if self.capture_action:
            text = (f" press a key to bind  ·  {self.capture_action}"
                    f"   [Ctrl-C] cancel ")
            self.write([self.bar(text, PROMPT_BG)])
            return
        if self.cfg.get("hide_ui"):
            self.write([f"{ESC}[{self.status_row};1H{ESC}[2K"])
            self.flash = ""
            return
        km = self.cfg["keymap"]

        def bk(a):
            return km.get("board." + a)

        def ck(a):
            return km.get("canvas." + a)

        if self.mode == "settings":
            text = (" SETTINGS   click a row to change   "
                    "scroll to navigate   Ctrl-C / Save & close to exit ")
            if self.flash:
                text = " " + self.flash + "   " + text
            self.write([self.bar(text[:self.cols], SETTINGS_BG)])
            self.flash = ""
            return
        if self.mode == "boards":
            text = (f" BOARDS  {len(self.board_list)} found   "
                    "↑/↓ or scroll navigate   [Enter] open   "
                    "[n] new   [q/Esc] back ")
            if self.flash:
                text = " " + self.flash + "   " + text
            self.write([self.bar(text[:self.cols], SETTINGS_BG)])
            self.flash = ""
            return
        if self.mode == "board":
            sel = self.node_by_id(self.selected)
            seltxt = sel["title"] if sel else "-"
            left = f" BOARD  {len(self.nodes)} node(s)  sel:{seltxt:<10} "
            right = self._hints([
                (None, "click select"), (None, "drag move"),
                (None, "right-click menu"), ("\r", "open"),
                (bk("new_node"), "new"), (bk("new_board"), "new-board"),
                (bk("link"), "link"), (bk("delete"), "del"),
                (bk("save"), "save"), (bk("open"), "open"),
                (bk("boards"), "boards"),
                (bk("settings"), "settings"), ("q", "quit"), ("?", "help")])
            if self.flash:
                right = "| " + self.flash + "  " + right
            text = (left + right)[:self.cols].ljust(self.cols)
            self.write([f"{ESC}[{self.status_row};1H{ESC}[48;5;{BAR_BG}m"
                        f"{ESC}[38;5;{BAR_FG}m{text}{ESC}[0m"])
            self.flash = ""
            return
        # canvas mode
        sw = chr(BRAILLE_BASE + 0xFF)
        r, g, b = self.color
        node = self.node_by_id(self.active_node)
        title = node["title"] if node else "?"
        left = (f" [{title[:12]}]  {self.tool.upper():<7} {sw} "
                f"{self.color_name:<6} e:{self.erase_r:<2} ")
        right = self._hints([
            (ck("erase"), "erase"), (ck("select"), "select"),
            (None, "[ ]/wheel size"), (None, "1-8 color"),
            (ck("undo"), "undo"), (ck("redo"), "redo"),
            (ck("clear"), "clear"), (ck("export"), "svg"),
            (ck("back"), "board"), ("?", "help")])
        if self.flash:
            right = "| " + self.flash + "  " + right
        text = (left + right)[:self.cols].ljust(self.cols)
        text = text.replace(
            sw, f"{ESC}[38;2;{r};{g};{b}m{sw}{ESC}[38;5;{BAR_FG}m", 1)
        self.write([f"{ESC}[{self.status_row};1H{ESC}[48;5;{BAR_BG}m"
                    f"{ESC}[38;5;{BAR_FG}m{text}{ESC}[0m"])
        self.flash = ""

    def _bkey(self, a):
        return self._keyname(self.cfg["keymap"].get("board." + a, "?"))

    def _ckey(self, a):
        return self._keyname(self.cfg["keymap"].get("canvas." + a, "?"))

    def help_lines(self):
        if self.mode == "board":
            return [
                "  draw — BOARD",
                "",
                "  click        select a node",
                "  drag         move a node",
                "  dbl-click    the [↗] tab (top-right) opens that node",
                "  right-click  menu: enter / rename / copy / link / delete",
                "               (on empty space: new node / new board)",
                "",
                f"  {self._bkey('new_node'):<5} new node       Enter  open selected node",
                f"  {self._bkey('new_board'):<5} new board      Tab    cycle selection",
                f"  {self._bkey('delete'):<5} delete node",
                f"  {self._bkey('link'):<5} link: then click another node to connect",
                f"  {self._bkey('rename'):<5} rename node    (copy a node via right-click)",
                "",
                f"  {self._bkey('save'):<5} save board     {self._bkey('open'):<5} open board",
                f"  {self._bkey('boards'):<5} browse & switch between saved boards",
                f"  {self._bkey('settings'):<5} settings       `      hide/show the UI bar",
                "  q     quit (asks to save if there are changes)",
                "",
                "  press any key to close",
            ]
        return [
            "  draw — CANVAS",
            "",
            "  left-drag   draw with current tool    right-drag  erase",
            "",
            f"  {self._ckey('free'):<3} freehand   {self._ckey('line'):<3} line       "
            f"{self._ckey('rect'):<3} rectangle",
            f"  {self._ckey('ellipse'):<3} ellipse    {self._ckey('arrow'):<3} arrow      "
            f"{self._ckey('erase'):<3} eraser",
            f"  {self._ckey('select'):<3} select / move — drag a box over shapes, then",
            "      drag the box to move them; right-click clears selection",
            "",
            "  [ / ]  or scroll-wheel   resize eraser (ring shows area)",
            "  1-8  pick color",
            f"  {self._ckey('undo'):<3} undo   {self._ckey('redo'):<3} redo   "
            f"{self._ckey('clear'):<3} clear   {self._ckey('export'):<3} export .svg",
            "",
            f"  {self._ckey('back')} / Tab / q   back to the board     `  hide/show UI",
            "  keys are remappable in Settings (board: , )",
            "",
            "  press any key to close",
        ]

    def open_help(self):
        self.help_open = True
        lines = self.help_lines()
        out = [f"{ESC}[2J"]
        top = max(1, (self.rows - len(lines)) // 2)
        for i, ln in enumerate(lines):
            if i == 0:
                out.append(f"{ESC}[{top + i};3H{ESC}[1m{ln}{ESC}[0m")
            else:
                out.append(f"{ESC}[{top + i};3H{ln}")
        self.write(out)

    def close_help(self):
        self.help_open = False
        self.write([f"{ESC}[2J"])
        self.displayed = {}
        self.txt = {}
        if self.mode == "board":
            self.render_board()
        elif self.mode == "settings":
            self.render_settings()
        elif self.mode == "boards":
            self.render_boards()
        else:
            self.rebuild_base()
            self.present()
        self.status()

    # ============================ RESIZE / LOOP ============================
    def handle_resize(self):
        self._measure()
        for n in self.nodes:
            n["bx"] = max(1, min(self.cols - n["w"] + 1, n["bx"]))
            n["by"] = max(1, min(self.status_row - n["h"], n["by"]))
        self.displayed = {}
        self.txt = {}
        self.write([f"{ESC}[2J"])
        if self.help_open:
            self.open_help()
        elif self.mode == "settings":
            self.render_settings()
            self.status()
        elif self.mode == "boards":
            self.render_boards()
            self.status()
        elif self.mode == "board":
            self.render_board()
            self.status()
        else:
            self.mouse_dot = (min(self.mouse_dot[0], self.dw - 1),
                              min(self.mouse_dot[1], self.dh - 1))
            self.rebuild_base()
            self.status()
            self.present()

    def handle_mouse(self, b, x, y, final):
        if (self.help_open or self.prompt_mode or self.capture_action
                or self.confirm is not None):
            return
        if self.mode == "settings":
            self.handle_settings_mouse(b, x, y, final)
        elif self.mode == "boards":
            self.handle_boards_mouse(b, x, y, final)
        elif self.mode == "board":
            self.handle_board_mouse(b, x, y, final)
        else:
            self.handle_canvas_mouse(b, x, y, final)

    def handle_key(self, ch):
        if self.confirm is not None:
            keys = {k for k, _ in self.confirm["options"]}
            if ch in keys:
                kind, data = self.confirm["kind"], self.confirm.get("data")
                self.confirm = None
                self.resolve_confirm(kind, ch, data)
            elif ch in ("\x03", "ESC"):
                self.confirm = None
                self.quit_after_save = False
                self.flash = "cancelled"
                self.status()
            return
        if self.prompt_mode:
            self.handle_prompt_key(ch)
            return
        if self.capture_action is not None:
            self.finish_capture(ch)
            return
        if self.menu is not None:
            if ch in ("\r", "\n"):
                self.run_menu(self.menu["hover"])
            else:
                self.close_menu()
            return
        if self.help_open:
            self.close_help()
            return
        if ch == "`":
            self.toggle_ui()
            return
        if self.mode == "settings":
            self.handle_settings_key(ch)
        elif self.mode == "boards":
            self.handle_boards_key(ch)
        elif self.mode == "board":
            self.handle_board_key(ch)
        else:
            self.handle_canvas_key(ch)

    def write(self, parts):
        if parts:
            sys.stdout.write("".join(parts))
            sys.stdout.flush()

    def run(self):
        old = termios.tcgetattr(self.fd)
        tty.setraw(self.fd)
        enable = f"{ESC}[?1049h{ESC}[?25l{ESC}[2J{ESC}[?1003h{ESC}[?1006h"
        if self.pixel_mode:
            enable += f"{ESC}[?1016h"
        sys.stdout.write(enable)
        sys.stdout.flush()
        if not self.nodes:
            self.autoload_board()
        if not self.nodes:
            self.new_node(self.cols // 2, self.rows // 2)
        self.dirty = False                    # fresh session isn't "unsaved" yet
        if self.canvas:
            # jump straight into a single canvas
            self.open_node(self.nodes[0])
        else:
            self.render_board()
            self.status()
        try:
            signal.signal(signal.SIGWINCH,
                          lambda *_: setattr(self, "resized", True))
            signal.siginterrupt(signal.SIGWINCH, True)
        except (ValueError, OSError):
            pass
        buf = ""
        try:
            while self.running:
                if self.resized:
                    self.resized = False
                    self.handle_resize()
                try:
                    chunk = os.read(self.fd, 4096).decode("utf-8", "ignore")
                except (InterruptedError, OSError):
                    continue
                if not chunk:
                    break
                buf += chunk
                i = 0
                while i < len(buf):
                    c = buf[i]
                    if c == ESC:
                        if buf[i:i + 3] == f"{ESC}[<":
                            m = MOUSE_RE.match(buf, i)
                            if not m:
                                break
                            self.handle_mouse(int(m.group(1)), int(m.group(2)),
                                              int(m.group(3)), m.group(4))
                            i = m.end()
                            continue
                        if len(buf) - i == 1:
                            self.handle_key("ESC")     # lone Esc keypress
                            i += 1
                            continue
                        if len(buf) - i < 3:
                            break
                        # arrow keys: ESC [ A/B/C/D  or  ESC O A/B/C/D
                        # (WezTerm sends these for the wheel in the alt-screen)
                        if buf[i + 1] in "[O" and buf[i + 2] in "ABCD":
                            self.handle_key({"A": "UP", "B": "DOWN",
                                             "C": "RIGHT", "D": "LEFT"}[buf[i + 2]])
                            i += 3
                            continue
                        i += 1
                        continue
                    self.handle_key(c)
                    i += 1
                buf = buf[i:]
        finally:
            disable = (f"{ESC}[?1016l{ESC}[?1006l{ESC}[?1003l"
                       f"{ESC}[?25h{ESC}[?1049l")
            sys.stdout.write(disable)
            sys.stdout.flush()
            termios.tcsetattr(self.fd, termios.TCSADRAIN, old)


if __name__ == "__main__":
    argv = sys.argv[1:]
    config_path = os.environ.get("DRAW_CONFIG")
    flags, positional = set(), []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in ("-c", "--config"):
            i += 1
            if i < len(argv):
                config_path = argv[i]
        elif a.startswith("--config="):
            config_path = a.split("=", 1)[1]
        elif a.startswith("-"):
            flags.add(a)
        else:
            positional.append(a)
        i += 1
    if "-h" in flags or "--help" in flags:
        print(USAGE)
        sys.exit(0)
    if not sys.stdin.isatty():
        sys.exit("Run this directly in a terminal (not piped).")
    canvas = bool(flags & {"-q", "--canvas", "--draw"})
    base = positional[0] if positional else "draw"
    App(base, canvas=canvas, config_path=config_path).run()
