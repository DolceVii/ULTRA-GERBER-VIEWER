#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ULTRA GERBER VIEWER by George Kourtidis
Pure Python 3 + PyQt6
Version v1
NO gerbv, NO external renderer.

Install:
    pip install PyQt6

Run:
    python UltraView1.py

Keys:
    F     FIT
    C     CENTER
    M     Measure
    Esc   Clear measure / exit measure
"""

from __future__ import annotations

import math
import re
import sys
import traceback
import zipfile
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, List, Tuple, Dict, Any

from PyQt6.QtCore import Qt, QPointF, QRectF, QSize, QTimer, QElapsedTimer, pyqtSignal, QMarginsF
from PyQt6.QtGui import (
    QAction, QColor, QPainter, QPen, QBrush, QPainterPath, QPixmap, QImage, QTransform,
    QWheelEvent, QMouseEvent, QKeySequence, QFont, QPolygonF, QPainterPathStroker,
    QPdfWriter, QPageSize, QPageLayout, QLinearGradient, QRadialGradient
)
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QFileDialog, QVBoxLayout, QHBoxLayout,
    QPushButton, QLabel, QColorDialog, QSplitter, QFrame, QTextEdit,
    QTableWidget, QTableWidgetItem, QHeaderView, QAbstractItemView,
    QStyledItemDelegate, QStyle
)

MM_PER_INCH = 25.4

# Realistic PCB export constants.  The PNG renderer uses these values to mimic
# the visual stack shown by common PCB/3D viewers: black background, matte green
# soldermask, ENIG-style gold exposed copper, black drill barrels and a subtle
# board-edge extrusion.
PCB_THICKNESS_MM = 1.5
REALISTIC_BG = QColor(0, 0, 0, 255)
REALISTIC_TOP_MASK_LIGHT = QColor(66, 205, 26, 255)
REALISTIC_TOP_MASK_MID = QColor(44, 170, 18, 255)
REALISTIC_TOP_MASK_DARK = QColor(16, 112, 9, 255)
REALISTIC_BOTTOM_MASK_LIGHT = QColor(58, 190, 24, 255)
REALISTIC_BOTTOM_MASK_MID = QColor(38, 150, 17, 255)
REALISTIC_BOTTOM_MASK_DARK = QColor(12, 92, 8, 255)
REALISTIC_COPPER_UNDER_MASK = QColor(23, 112, 20, 255)
REALISTIC_COPPER_TRACE = QColor(33, 138, 22, 255)
REALISTIC_GOLD_LIGHT = QColor(255, 226, 92, 255)
REALISTIC_GOLD_MID = QColor(235, 178, 31, 255)
REALISTIC_GOLD_DARK = QColor(138, 86, 8, 255)
REALISTIC_SILK = QColor(245, 255, 238, 255)
REALISTIC_HOLE = QColor(0, 0, 0, 255)
REALISTIC_HOLE_RIM = QColor(16, 42, 10, 255)
REALISTIC_EDGE_LIGHT = QColor(195, 255, 185, 230)
REALISTIC_EDGE_SIDE = QColor(24, 92, 13, 255)
REALISTIC_EDGE_SIDE_DARK = QColor(6, 52, 7, 255)

GERBER_EXTS = {
    # Standard / generic RS-274X
    ".gbr", ".ger", ".pho", ".art", ".gbx",
    # Standard Gerber X2 / common fab-house names
    ".gtl", ".gbl", ".g1", ".g2", ".g3", ".g4", ".g5", ".g6",
    ".gp1", ".gp2", ".gp3", ".gp4", ".gpb", ".gpt", ".gtp",
    ".gts", ".gbs", ".gto", ".gbo", ".gbp",
    ".gko", ".gm1", ".gm2", ".gm3", ".gm4", ".gml", ".fab",
    # Eagle / OSH Park / older CAM naming
    ".sol", ".cmp", ".stc", ".sts", ".crc", ".crs", ".plc", ".pls",
    # Vendor-specific or old CAD exports often found in Proteus, PADS, DipTrace, Sprint/Target/Ultiboard
    ".top", ".bot", ".smt", ".smb", ".sst", ".ssb", ".spt", ".spb",
    ".l1", ".l2", ".l3", ".l4", ".l5", ".l6", ".lyr", ".out", ".oln", ".dim",
}
DRILL_EXTS = {".drl", ".xln", ".nc", ".tap", ".ncd", ".nct", ".exc", ".excellon"}
CAM_METADATA_EXTS = {".rep", ".extrep", ".apr", ".apr_lib", ".ldp", ".gbrjob", ".rul", ".cam"}
CAM_OPEN_EXTS = GERBER_EXTS | DRILL_EXTS | {".txt"}


@dataclass
class Aperture:
    code: str
    kind: str
    params: List[float]

    def size(self) -> float:
        vals = [abs(v) for v in self.params if isinstance(v, (int, float))]
        return max(vals) if vals else 0.10


@dataclass
class Primitive:
    kind: str
    points: list = field(default_factory=list)
    width: float = 0.0
    rect: Optional[Tuple[float, float]] = None
    radius: float = 0.0
    contours: Optional[List[List[QPointF]]] = None


@dataclass
class Layer:
    name: str
    path: str
    color: QColor
    primitives: List[Primitive] = field(default_factory=list)
    visible: bool = True
    bbox: QRectF = field(default_factory=lambda: QRectF())
    info: str = ""


class GerberParser:
    def __init__(self):
        self.unit = "mm"
        self.abs_mode = True
        self.x_int = 2
        self.x_dec = 5
        self.y_int = 2
        self.y_dec = 5

        self.apertures: Dict[str, Aperture] = {}
        self.aperture_macros: Dict[str, str] = {}
        self.aperture_param_hints: Dict[str, Dict[str, float | str]] = {}
        self.current_ap = "10"
        self.current_op = "D02"
        self.interp = "G01"

        self.x = 0.0
        self.y = 0.0

        self.region = False
        self.polarity = "dark"
        self.image_polarity = "positive"   # RS-274X IPPOS/IPNEG image polarity
        self.legacy_altium_mode = False      # only enables CAMtastic/old Altium special hacks
        self.region_contours: List[List[QPointF]] = []
        self.current_contour: List[QPointF] = []

        self.primitives: List[Primitive] = []
        self.debug = {"cmd": 0, "ap": 0, "move": 0, "draw": 0, "flash": 0, "region": 0, "fallback": 0}

    def detect_legacy_altium_mode(self, path: str, text: str) -> bool:
        """Detect old Altium/CAMtastic/Protel style Gerbers.

        Keep KiCad/modern RS-274X on the stable v8 parser path.  The special
        thermal/IPNEG/THD handling is activated only for files that really look
        like legacy Altium CAM output, because those hacks can corrupt KiCad
        aperture macros and create ghost circles or inverted copper.
        """
        name = Path(path).name.upper()
        suffix = Path(path).suffix.upper()
        head = text[:250000].upper()
        legacy_markers = (
            "AMTHD", "THD52", "THD53",
            "THERMALRELIEF", "SHAPE=THERMAL",
            "%IPNEG", "IPNEG",
        )
        legacy_exts = {".GP1", ".GP2", ".GP3", ".GP4", ".GPB", ".GPT"}
        return suffix in legacy_exts or any(m in head for m in legacy_markers)

    def parse_file(self, path: str) -> List[Primitive]:
        text = Path(path).read_text(errors="ignore")
        self.legacy_altium_mode = self.detect_legacy_altium_mode(path, text)
        self.pre_scan_altium_macros(text)
        for cmd in self.split_commands(text):
            self.debug["cmd"] += 1
            self.parse_cmd(cmd)

        if not self.primitives:
            self.primitives = self.fallback_preview(text)
            self.debug["fallback"] = len(self.primitives)

        return self.primitives

    def pre_scan_altium_macros(self, text: str):
        """Pre-scan AM macro bodies and Altium G04:AMPARAMS comments.

        Altium Designer exports rounded/rotated SMD pads as aperture macros:
            G04:AMPARAMS|DCode=26|XSize=0.28mm|YSize=1.47mm|...|Shape=RoundedRectangle|*
            %AMROUNDEDRECTD26* ... %
            %ADD26ROUNDEDRECTD26*%
        A simple RS-274X splitter usually sees only ADD26 with no numeric
        parameters, so the pad becomes a tiny fallback. This scan preserves
        the real geometry before normal command parsing.
        """
        for line in text.splitlines():
            line = line.strip()
            if "AMPARAMS" not in line or "DCode=" not in line:
                continue
            parts = {}
            for token in line.replace("G04:", "").replace("*", "").split("|"):
                if "=" in token:
                    k, v = token.split("=", 1)
                    parts[k.strip()] = v.strip()
            code = parts.get("DCode")
            if not code:
                continue

            def mm_value(key: str, default: float = 0.0) -> float:
                raw = parts.get(key, str(default)).strip().lower()
                try:
                    if raw.endswith("mil"):
                        return float(raw[:-3]) * MM_PER_INCH / 1000.0
                    if raw.endswith("inch") or raw.endswith("in"):
                        raw = raw.replace("inch", "").replace("in", "")
                        return float(raw) * MM_PER_INCH
                    if raw.endswith("mm"):
                        raw = raw[:-2]
                    return float(raw)
                except Exception:
                    return default

            self.aperture_param_hints[str(int(code))] = {
                "x": mm_value("XSize"),
                "y": mm_value("YSize"),
                "corner": mm_value("CornerRadius"),
                "rot": mm_value("Rotation"),
                "gap": mm_value("Gap"),
                "width": mm_value("Width"),
                "shape": parts.get("Shape", "").upper(),
            }

        for m in re.finditer(r"%AM([^*%]+)\*(.*?)%", text, re.S):
            name = m.group(1).upper().strip()
            body = m.group(2).strip()
            if name:
                self.aperture_macros[name] = body

    @staticmethod
    def rotate_point(px: float, py: float, deg: float) -> tuple[float, float]:
        if abs(deg) < 1e-12:
            return px, py
        a = math.radians(deg)
        ca, sa = math.cos(a), math.sin(a)
        return px * ca - py * sa, px * sa + py * ca

    @staticmethod
    def macro_eval(token: str, params: List[float]) -> float:
        """Evaluate the tiny arithmetic KiCad/RS-274X aperture macros use.

        KiCad 10 writes RoundRect as an AM macro with variables like $1+$1,
        $2, $3 ... and then calls it with %ADDnnRoundRect,...*%.  The old
        preview treated those tokens as non-numeric and fell back to a wrong
        rectangle/octagon.  This evaluator intentionally supports only safe
        numeric expressions: constants, $variables and + - * / parentheses.
        """
        expr = token.strip()
        if not expr:
            return 0.0

        def repl(m):
            idx = int(m.group(1)) - 1
            return str(float(params[idx]) if 0 <= idx < len(params) else 0.0)

        expr = re.sub(r"\$(\d+)", repl, expr)
        if not re.fullmatch(r"[0-9eE+\-*/(). ]+", expr):
            raise ValueError(f"unsafe macro token: {token}")
        return float(eval(expr, {"__builtins__": {}}, {}))

    def polygon_rect(self, x: float, y: float, w: float, h: float, rot: float = 0.0) -> Primitive:
        hw, hh = w / 2.0, h / 2.0
        pts = []
        for px, py in [(-hw, -hh), (hw, -hh), (hw, hh), (-hw, hh)]:
            rx, ry = self.rotate_point(px, py, rot)
            pts.append(QPointF(x + rx, y + ry))
        return Primitive("polygon", points=pts)

    @staticmethod
    def thermal_relief_polygons(x: float, y: float, outer_d: float, inner_d: float, gap: float, rot_deg: float = 0.0) -> List[List[QPointF]]:
        """Approximate RS-274X AM primitive 7 thermal relief as four filled sectors.

        Primitive 7 is used by older Altium/CAMtastic internal plane files
        (*.GP1, *.GP2). If it is ignored, thermal apertures either disappear or
        become wrong solid dots.  Four annular sectors are enough for visual CAM
        inspection and do not affect other aperture types.
        """
        outer_r = max(abs(outer_d) / 2.0, 1e-6)
        inner_r = max(abs(inner_d) / 2.0, 0.0)
        if inner_r >= outer_r:
            inner_r = outer_r * 0.65

        mean_r = max((outer_r + inner_r) / 2.0, 1e-6)
        gap_ang = max(4.0, min(42.0, math.degrees(abs(gap) / mean_r)))
        half_gap = gap_ang / 2.0
        rot = rot_deg
        sectors = []
        for base in (0.0, 90.0, 180.0, 270.0):
            a0 = math.radians(base + half_gap + rot)
            a1 = math.radians(base + 90.0 - half_gap + rot)
            steps = 18
            pts = []
            for k in range(steps + 1):
                a = a0 + (a1 - a0) * k / steps
                pts.append(QPointF(x + outer_r * math.cos(a), y + outer_r * math.sin(a)))
            for k in range(steps, -1, -1):
                a = a0 + (a1 - a0) * k / steps
                pts.append(QPointF(x + inner_r * math.cos(a), y + inner_r * math.sin(a)))
            if len(pts) >= 3:
                sectors.append(pts)
        return sectors

    def emit_thermal_flash(self, x: float, y: float, outer_d: float, inner_d: float, gap: float, rot: float = 45.0) -> bool:
        """Emit a real thermal relief flash for Altium/CAMtastic GP1/GP2 layers.

        The old fallback converted THD52/THD53 into normal filled circles, so
        internal plane relief pads in .GP1/.GP2 looked solid.  Keep the thermal
        as a first-class primitive so the renderer can draw the four copper
        islands and leave the centre/spoke clearances transparent.
        """
        if outer_d <= 0:
            return False
        if inner_d <= 0 or inner_d >= outer_d:
            inner_d = outer_d * 0.72
        if gap <= 0:
            gap = outer_d * 0.11
        prim = Primitive("thermal", points=[QPointF(x, y)], radius=outer_d / 2.0)
        prim.outer_d = float(outer_d)
        prim.inner_d = float(inner_d)
        prim.gap = float(gap)
        prim.rotation = float(rot)
        self.emit(prim)
        return True

    def thermal_from_aperture_hint_or_macro(self, ap: Aperture) -> Optional[Tuple[float, float, float, float]]:
        hint = self.aperture_param_hints.get(ap.code, {})
        shape = str(hint.get("shape", "")).upper()
        if "RELIEF" in shape:
            od = float(hint.get("x", 0.0) or hint.get("y", 0.0) or 0.0)
            gap = float(hint.get("gap", 0.0) or 0.0)
            if gap <= 0:
                gap = 0.254
            inner = max(od - 2.0 * gap, od * 0.72) if od > 0 else 0.0
            rot = float(hint.get("rot", 45.0) or 45.0)
        else:
            od = inner = gap = 0.0
            rot = 45.0

        macro = self.aperture_macros.get(ap.kind.upper(), "")
        for raw in macro.split("*"):
            line = raw.strip()
            if not line.startswith("7,"):
                continue
            vals = []
            ok = True
            for t in line.split(','):
                try:
                    vals.append(self.macro_eval(t.strip(), ap.params))
                except Exception:
                    ok = False
                    break
            if ok and len(vals) >= 7:
                if len(vals) >= 8:
                    _cx, _cy, mod, mid, mgap, mrot = vals[2], vals[3], vals[4], vals[5], vals[6], vals[7]
                else:
                    mod, mid, mgap, mrot = vals[3], vals[4], vals[5], vals[6]
                if self.unit == "inch" and not ap.params:
                    mod *= MM_PER_INCH
                    mid *= MM_PER_INCH
                    mgap *= MM_PER_INCH
                od, inner, gap, rot = abs(mod), abs(mid), abs(mgap), float(mrot)
                break

        return (od, inner, gap, rot) if od > 0 else None

    def flash_macro(self, ap: Aperture, x: float, y: float) -> bool:
        """Render common RS-274X aperture macro primitives.

        Supports the primitives Altium uses in this job:
        1 = circle, 21 = center-line rectangle, 4 = outline polygon.
        Clear/boolean macro composition is approximated visually, which is fine
        for a CAM viewer whose first job is not to lose pads.
        """
        macro = self.aperture_macros.get(ap.kind.upper())
        hint = self.aperture_param_hints.get(ap.code, {})

        if not macro and hint:
            sx = float(hint.get("x", 0.0) or 0.0)
            sy = float(hint.get("y", 0.0) or 0.0)
            rot = float(hint.get("rot", 0.0) or 0.0)
            shape = str(hint.get("shape", ""))
            if sx > 0 and sy > 0:
                if "ROUND" in shape:
                    self.emit(self.polygon_rect(x, y, sx, sy, rot))
                else:
                    self.emit(self.polygon_rect(x, y, sx, sy, rot))
                return True

        if not macro:
            return False

        emitted = False
        for raw in macro.split("*"):
            line = raw.strip()
            if not line:
                continue
            vals = []
            ok = True
            for t in line.split(','):
                t = t.strip()
                if not t:
                    continue
                try:
                    vals.append(self.macro_eval(t, ap.params))
                except Exception:
                    ok = False
                    break
            if not ok or not vals:
                continue

            prim = int(vals[0])
            exposure = int(vals[1]) if len(vals) > 1 else 1
            old_pol = self.polarity
            macro_pol = "clear" if exposure == 0 else old_pol

            def emit_macro(obj: Primitive):
                if self.legacy_altium_mode:
                    obj.polarity = macro_pol
                    try:
                        obj.aperture_code = str(self.current_ap)
                    except Exception:
                        pass
                    self.primitives.append(obj)
                else:
                    self.emit(obj)

            if (not self.legacy_altium_mode) and exposure == 0:
                self.polarity = "clear"

            if prim == 1 and len(vals) >= 5:
                d, cx, cy = vals[2], vals[3], vals[4]
                rot = vals[5] if len(vals) > 5 else 0.0
                rx, ry = self.rotate_point(cx, cy, rot)
                emit_macro(Primitive("circle", points=[QPointF(x + rx, y + ry)], radius=abs(d) / 2.0))
                emitted = True

            elif prim == 20 and len(vals) >= 7:
                w, x1, y1, x2, y2 = vals[2], vals[3], vals[4], vals[5], vals[6]
                rot = vals[7] if len(vals) > 7 else 0.0
                rx1, ry1 = self.rotate_point(x1, y1, rot)
                rx2, ry2 = self.rotate_point(x2, y2, rot)
                emit_macro(Primitive("line", points=[QPointF(x + rx1, y + ry1), QPointF(x + rx2, y + ry2)], width=abs(w)))
                emitted = True

            elif prim == 21 and len(vals) >= 7:
                w, h, cx, cy, rot = vals[2], vals[3], vals[4], vals[5], vals[6]
                rcx, rcy = self.rotate_point(cx, cy, rot)
                emit_macro(self.polygon_rect(x + rcx, y + rcy, abs(w), abs(h), rot))
                emitted = True

            elif prim == 4 and len(vals) >= 5:
                n = int(vals[2])
                coord_end = 3 + (n + 1) * 2
                coords = vals[3:coord_end]
                rot = vals[coord_end] if len(vals) > coord_end else 0.0

                if len(coords) >= 6 and len(coords) % 2 == 0:
                    pts = []
                    for i in range(0, len(coords), 2):
                        rx, ry = self.rotate_point(coords[i], coords[i + 1], rot)
                        pts.append(QPointF(x + rx, y + ry))

                    if len(pts) >= 2:
                        if abs(pts[0].x() - pts[-1].x()) < 1e-9 and abs(pts[0].y() - pts[-1].y()) < 1e-9:
                            pts.pop()

                    if len(pts) >= 3:
                        emit_macro(Primitive("polygon", points=pts))
                        emitted = True

            elif prim == 5 and len(vals) >= 7:
                n = max(3, int(vals[2]))
                cx, cy, d, rot = vals[3], vals[4], vals[5], vals[6]
                pts = []
                for a in range(n):
                    px = (d / 2.0) * math.cos(2 * math.pi * a / n)
                    py = (d / 2.0) * math.sin(2 * math.pi * a / n)
                    rx, ry = self.rotate_point(px + cx, py + cy, rot)
                    pts.append(QPointF(x + rx, y + ry))
                emit_macro(Primitive("polygon", points=pts))
                emitted = True

            elif prim == 7 and len(vals) >= 7:
                if len(vals) >= 8:
                    cx, cy, od, id_, gap = vals[2], vals[3], vals[4], vals[5], vals[6]
                    rot = vals[7]
                else:
                    cx, cy = vals[2], 0.0
                    od, id_, gap = vals[3], vals[4], vals[5]
                    rot = vals[6]

                if self.unit == "inch" and not ap.params:
                    cx *= MM_PER_INCH
                    cy *= MM_PER_INCH
                    od *= MM_PER_INCH
                    id_ *= MM_PER_INCH
                    gap *= MM_PER_INCH
                rcx, rcy = self.rotate_point(cx, cy, rot)

                self.polarity = old_pol
                for pts in self.thermal_relief_polygons(x + rcx, y + rcy, od, id_, gap, rot):
                    emit_macro(Primitive("polygon", points=pts))
                emitted = True

            self.polarity = old_pol

        return emitted

    @staticmethod
    def split_commands(text: str) -> List[str]:
        text = text.replace("\r", "")
        out, buf, ext = [], "", False

        for ch in text:
            if ch == "%":
                if ext:
                    for p in buf.split("*"):
                        p = p.strip()
                        if p:
                            out.append("%" + p + "%")
                    buf, ext = "", False
                else:
                    for p in buf.split("*"):
                        p = p.strip()
                        if p:
                            out.append(p)
                    buf, ext = "", True
                continue

            if ch == "*" and not ext:
                if buf.strip():
                    out.append(buf.strip())
                buf = ""
            else:
                buf += ch

        if buf.strip():
            for p in buf.split("*"):
                p = p.strip()
                if p:
                    out.append(("%" + p + "%") if ext else p)

        final = []
        for x in out:
            for line in x.splitlines():
                line = line.strip().replace(" ", "")
                if line:
                    final.append(line)
        return final

    def coord(self, raw: str, axis: str) -> float:
        if "." in raw:
            v = float(raw)
        else:
            dec = self.x_dec if axis == "X" else self.y_dec
            sign = -1 if raw.startswith("-") else 1
            s = raw.lstrip("+-") or "0"
            v = sign * int(s) / (10 ** dec)
        return v * MM_PER_INCH if self.unit == "inch" else v

    def parse_cmd(self, cmd: str):
        if not cmd:
            return

        if cmd.startswith("G04") or cmd.startswith("G4"):
            return

        if cmd.startswith("%") and cmd.endswith("%"):
            self.parse_ext(cmd[1:-1])
            return

        if "MOIN" in cmd or "G70" in cmd:
            self.unit = "inch"
        if "MOMM" in cmd or "G71" in cmd:
            self.unit = "mm"
        if "G90" in cmd:
            self.abs_mode = True
        if "G91" in cmd:
            self.abs_mode = False

        if re.search(r"(^|[^0-9])G0?1([^0-9]|$)", cmd):
            self.interp = "G01"
        elif re.search(r"(^|[^0-9])G0?2([^0-9]|$)", cmd):
            self.interp = "G02"
        elif re.search(r"(^|[^0-9])G0?3([^0-9]|$)", cmd):
            self.interp = "G03"

        if "G36" in cmd:
            self.region = True
            self.region_contours = []
            self.current_contour = []
            self.current_op = "D02"
            return

        if "G37" in cmd:
            self.finish_current_contour()
            if self.region_contours:
                self.emit(Primitive("region", contours=[list(c) for c in self.region_contours]))
                self.debug["region"] += 1
            self.region = False
            self.region_contours = []
            self.current_contour = []
            return

        sel = re.fullmatch(r"(?:G54)?D0?(\d+)", cmd)
        if sel and int(sel.group(1)) >= 10:
            self.current_ap = sel.group(1)
            return

        mx = re.search(r"X([+\-]?\d+(?:\.\d+)?)", cmd)
        my = re.search(r"Y([+\-]?\d+(?:\.\d+)?)", cmd)
        mi = re.search(r"I([+\-]?\d+(?:\.\d+)?)", cmd)
        mj = re.search(r"J([+\-]?\d+(?:\.\d+)?)", cmd)

        md = re.search(r"D0?([123])", cmd)
        standalone_d03 = re.fullmatch(r"(?:G54)?D0?3", cmd) is not None
        if md:
            self.current_op = "D0" + md.group(1)

        if not (mx or my):
            if standalone_d03:
                self.flash(self.x, self.y)
            return

        nx, ny = self.x, self.y
        if mx:
            val = self.coord(mx.group(1), "X")
            nx = val if self.abs_mode else self.x + val
        if my:
            val = self.coord(my.group(1), "Y")
            ny = val if self.abs_mode else self.y + val

        i = self.coord(mi.group(1), "X") if mi else 0.0
        j = self.coord(mj.group(1), "Y") if mj else 0.0

        if self.current_op == "D02":
            if self.region:
                self.finish_current_contour()
                self.current_contour = [QPointF(nx, ny)]
            self.x, self.y = nx, ny
            self.debug["move"] += 1
            return

        if self.current_op == "D03":
            self.flash(nx, ny)
            self.x, self.y = nx, ny
            return

        self.draw(nx, ny, i, j)
        self.x, self.y = nx, ny

    def finish_current_contour(self):
        if len(self.current_contour) >= 3:
            if self.current_contour[0] != self.current_contour[-1]:
                self.current_contour.append(QPointF(self.current_contour[0]))
            self.region_contours.append(list(self.current_contour))
        self.current_contour = []

    def parse_ext(self, body: str):
        if body.startswith("AM"):
            m = re.match(r"AM([^*%]+)\*(.*)", body, re.S)
            if m:
                self.aperture_macros[m.group(1).upper().strip()] = m.group(2)
            return

        if body.startswith("MOIN"):
            self.unit = "inch"
            return
        if body.startswith("MOMM"):
            self.unit = "mm"
            return

        if body.startswith("IPPOS"):
            self.image_polarity = "positive"
            return
        if body.startswith("IPNEG"):
            self.image_polarity = "negative"
            return

        if body.startswith("LPD"):
            self.polarity = "dark"
            return
        if body.startswith("LPC"):
            self.polarity = "clear"
            return

        fs = re.search(r"FS[LT]?A?X(\d)(\d)Y(\d)(\d)", body)
        if fs:
            self.x_int, self.x_dec, self.y_int, self.y_dec = map(int, fs.groups())
            return

        ad = re.match(r"ADD(\d+)([^,\*%]+)(?:,(.*))?$", body)
        if ad:
            code = ad.group(1)
            kind = ad.group(2).upper().strip()
            params = ad.group(3) or ""
            nums = []
            for t in re.split(r"[Xx,]", params):
                t = t.strip()
                if not t:
                    continue
                try:
                    v = float(t)
                    nums.append(v * MM_PER_INCH if self.unit == "inch" else v)
                except Exception:
                    pass

            hint = self.aperture_param_hints.get(str(int(code)))
            if not nums and hint:
                sx = float(hint.get("x", 0.0) or 0.0)
                sy = float(hint.get("y", 0.0) or 0.0)
                rot = float(hint.get("rot", 0.0) or 0.0)
                corner = float(hint.get("corner", 0.0) or 0.0)
                nums = [sx, sy, rot, corner]

            self.apertures[code] = Aperture(code, kind, nums)
            self.debug["ap"] += 1

    def emit(self, prim: Primitive):
        prim.polarity = self.polarity
        try:
            prim.aperture_code = str(self.current_ap)
        except Exception:
            pass
        self.primitives.append(prim)

    def draw(self, nx: float, ny: float, i: float, j: float):
        if self.region:
            if not self.current_contour:
                self.current_contour.append(QPointF(self.x, self.y))
            if self.interp in ("G02", "G03") and (abs(i) > 1e-12 or abs(j) > 1e-12):
                pts = self.arc(self.x, self.y, nx, ny, i, j, self.interp == "G03")
                self.current_contour.extend(QPointF(px, py) for px, py in pts[1:])
            else:
                self.current_contour.append(QPointF(nx, ny))
            return

        width = self.apertures.get(self.current_ap, Aperture("x", "C", [0.10])).size()

        if self.interp in ("G02", "G03") and (abs(i) > 1e-12 or abs(j) > 1e-12):
            pts = self.arc(self.x, self.y, nx, ny, i, j, self.interp == "G03")
            self.emit(Primitive("polyline", points=[QPointF(px, py) for px, py in pts], width=width))
        else:
            self.emit(Primitive("line", points=[QPointF(self.x, self.y), QPointF(nx, ny)], width=width))
        self.debug["draw"] += 1

    def flash(self, x: float, y: float):
        ap = self.apertures.get(self.current_ap)
        if not ap:
            self.emit(Primitive("circle", points=[QPointF(x, y)], radius=0.10))
            self.debug["flash"] += 1
            return

        k, p = ap.kind.upper(), ap.params

        if self.legacy_altium_mode and (k.startswith("THD") or str(ap.code) in {"52", "53"}):
            thermal_params = self.thermal_from_aperture_hint_or_macro(ap)
            if thermal_params is not None:
                od, inner, gap, rot = thermal_params
                if self.emit_thermal_flash(x, y, od, inner, gap, rot):
                    self.debug["flash"] += 1
                    return

        thermal_params = self.thermal_from_aperture_hint_or_macro(ap) if self.legacy_altium_mode else None
        if thermal_params is not None:
            od, inner, gap, rot = thermal_params
            if self.emit_thermal_flash(x, y, od, inner, gap, rot):
                self.debug["flash"] += 1
                return

        if k in self.aperture_macros or ap.code in self.aperture_param_hints:
            if self.flash_macro(ap, x, y):
                self.debug["flash"] += 1
                return

        if k == "C":
            d = p[0] if p else 0.20
            self.emit(Primitive("circle", points=[QPointF(x, y)], radius=d / 2))
        elif k == "R":
            w = p[0] if len(p) > 0 else 0.20
            h = p[1] if len(p) > 1 else w
            self.emit(Primitive("rect", points=[QPointF(x, y)], rect=(w, h)))
        elif k == "O":
            w = p[0] if len(p) > 0 else 0.20
            h = p[1] if len(p) > 1 else w
            self.emit(Primitive("obround", points=[QPointF(x, y)], rect=(w, h)))
        elif k == "P":
            d = p[0] if len(p) > 0 else 0.20
            n = max(3, int(p[1]) if len(p) > 1 else 6)
            rot = math.radians(p[2]) if len(p) > 2 else 0
            r = d / 2
            pts = [
                QPointF(x + r * math.cos(rot + 2 * math.pi * a / n),
                        y + r * math.sin(rot + 2 * math.pi * a / n))
                for a in range(n)
            ]
            self.emit(Primitive("polygon", points=pts))
        elif k.startswith("OC"):
            d = p[0] if p else 0.20
            n = 8
            rot = math.radians(22.5)
            r = d / 2
            pts = [
                QPointF(x + r * math.cos(rot + 2 * math.pi * a / n),
                        y + r * math.sin(rot + 2 * math.pi * a / n))
                for a in range(n)
            ]
            self.emit(Primitive("polygon", points=pts))
        else:
            d = p[0] if p else 0.20
            macro_name = k.upper()

            if len(p) >= 2 and ("RECT" in macro_name or "SQUARE" in macro_name or "RNDREC" in macro_name):
                self.emit(self.polygon_rect(x, y, p[0], p[1], p[2] if len(p) > 2 else 0.0))
            elif len(p) >= 2 and abs(p[0] - p[1]) > 1e-9:
                self.emit(self.polygon_rect(x, y, p[0], p[1], p[2] if len(p) > 2 else 0.0))
            else:
                n = 8
                rot = math.radians(22.5)
                r = d / 2
                pts = [
                    QPointF(x + r * math.cos(rot + 2 * math.pi * a / n),
                            y + r * math.sin(rot + 2 * math.pi * a / n))
                    for a in range(n)
                ]
                self.emit(Primitive("polygon", points=pts))
        self.debug["flash"] += 1

    @staticmethod
    def arc(x0, y0, x1, y1, i, j, ccw=True):
        cx, cy = x0 + i, y0 + j
        r = math.hypot(x0 - cx, y0 - cy)
        if r <= 1e-12:
            return [(x0, y0), (x1, y1)]

        a0 = math.atan2(y0 - cy, x0 - cx)
        a1 = math.atan2(y1 - cy, x1 - cx)

        if ccw and a1 <= a0:
            a1 += 2 * math.pi
        if not ccw and a1 >= a0:
            a1 -= 2 * math.pi

        steps = max(12, min(240, int(abs(a1 - a0) * r * 12)))
        return [
            (cx + r * math.cos(a0 + (a1-a0)*k/steps),
             cy + r * math.sin(a0 + (a1-a0)*k/steps))
            for k in range(steps + 1)
        ]

    def fallback_preview(self, text: str) -> List[Primitive]:
        prims, x, y, op = [], None, None, "D02"
        for cmd in self.split_commands(text):
            md = re.search(r"D0?([123])", cmd)
            if md:
                op = "D0" + md.group(1)

            mx = re.search(r"X([+\-]?\d+(?:\.\d+)?)", cmd)
            my = re.search(r"Y([+\-]?\d+(?:\.\d+)?)", cmd)
            if not (mx or my):
                continue

            nx = x if x is not None else 0
            ny = y if y is not None else 0
            if mx:
                nx = self.coord(mx.group(1), "X")
            if my:
                ny = self.coord(my.group(1), "Y")

            if x is not None and y is not None and op == "D01":
                prims.append(Primitive("line", points=[QPointF(x, y), QPointF(nx, ny)], width=0.08))
            elif op == "D03":
                prims.append(Primitive("circle", points=[QPointF(nx, ny)], radius=0.10))

            x, y = nx, ny
        return prims


LegacyAltiumGerberParser = GerberParser


class ExcellonParser:
    def emit(self, prim: Primitive):
        self._prims_target.append(prim)

    def __init__(self):
        self.unit = "inch"
        self.decimals = 4
        self.tools: Dict[str, float] = {}
        self.tool = None
        self.info = ""
        self.format_locked = False

    def parse_file(self, path: str) -> List[Primitive]:
        text = Path(path).read_text(errors="ignore")
        lines = text.splitlines()

        name = Path(path).name.upper()
        head = text[:200000].upper()
        self.kicad_decimal_inch = ("KICAD" in head and "INCH" in head and "DECIMAL" in head)

        # Altium Designer commonly exports drill/slot files as *.TXT with
        # METRIC,TZ coordinates but without an explicit FILE_FORMAT line.
        # In that case the coordinate format is normally 2:4 / 4 decimal
        # places.  The old parser defaulted METRIC to 3 decimals, so values
        # like X127651/Y549295 became 127.651/549.295 mm instead of
        # 12.7651/54.9295 mm, which throws RoundHoles/SlotHoles far outside
        # the PCB.
        self.altium_txt_metric_hint = (
            Path(path).suffix.upper() == ".TXT"
            and (
                "ALTIUM" in head
                or "ROUNDHOLES" in name
                or "SLOTHOLES" in name
                or "PLATED" in name
                or "NONPLATED" in name
                or "NON-PLATED" in name
            )
        )

        prims = self._parse_lines(lines)

        if self.unit == "inch" and self.decimals == 4 and self._looks_too_large(prims):
            self.decimals = 5
            self.tools = {}
            self.tool = None
            prims = self._parse_lines(lines)
            self.info = "Excellon inch auto format: 1.5 / 5 decimals"
        else:
            extra = " KiCad decimal-inch" if getattr(self, "kicad_decimal_inch", False) else ""
            if getattr(self, "altium_txt_metric_hint", False) and self.unit == "mm" and self.decimals == 4:
                extra += " Altium TXT metric 2:4"
            self.info = f"Excellon {self.unit} decimals={self.decimals}{extra}"

        return prims

    def _parse_lines(self, lines: List[str]) -> List[Primitive]:
        prims = []
        self._prims_target = prims
        last_x = None
        last_y = None
        route_mode = False   # Excellon routed slots between M15/M16
        for raw in lines:
            line = raw.strip().upper().replace(" ", "")
            if not line:
                continue

            fmt = re.search(r"FILE_FORMAT\s*=\s*(\d+)\s*:\s*(\d+)", line)
            if fmt:
                self.decimals = int(fmt.group(2))
                self.format_locked = True
                if line.startswith(";"):
                    continue

            if line.startswith(";"):
                continue

            if line == "M15":
                route_mode = True
                continue
            if line == "M16":
                route_mode = False
                continue

            fmt = re.search(r"FILE_FORMAT\s*=\s*(\d+)\s*:\s*(\d+)", line)
            if fmt:
                self.decimals = int(fmt.group(2))
                self.format_locked = True

            if "METRIC" in line:
                self.unit = "mm"
                if not self.format_locked:
                    self.decimals = 4 if getattr(self, "altium_txt_metric_hint", False) else 3
            if "INCH" in line or "M72" in line:
                self.unit = "inch"

            mt = re.match(r"T(\d+)C([0-9.]+)", line)
            if mt:
                d = float(mt.group(2))
                self.tools[mt.group(1)] = d * MM_PER_INCH if self.unit == "inch" else d
                continue

            ms = re.fullmatch(r"T(\d+)", line)
            if ms:
                self.tool = ms.group(1)
                continue

            mx = re.search(r"X([+\-]?(?:\d+(?:\.\d*)?|\.\d+))", line)
            my = re.search(r"Y([+\-]?(?:\d+(?:\.\d*)?|\.\d+))", line)

            prev_x, prev_y = last_x, last_y
            if mx:
                last_x = self.num(mx.group(1))
            if my:
                last_y = self.num(my.group(1))

            if (mx or my) and last_x is not None and last_y is not None:
                dia = self.tools.get(self.tool or "", 0.35)
                if route_mode and prev_x is not None and prev_y is not None:
                    prims.append(Primitive("line", points=[QPointF(prev_x, prev_y), QPointF(last_x, last_y)], width=dia))
                else:
                    prims.append(Primitive("circle", points=[QPointF(last_x, last_y)], radius=dia / 2))
        return prims

    @staticmethod
    def _looks_too_large(prims: List[Primitive]) -> bool:
        if len(prims) < 2:
            return False
        xs = [p.points[0].x() for p in prims if p.points]
        ys = [p.points[0].y() for p in prims if p.points]
        if not xs or not ys:
            return False
        w = max(xs) - min(xs)
        h = max(ys) - min(ys)
        return max(w, h) > 300.0

    def num(self, s: str) -> float:
        v = float(s) if "." in s else int(s) / (10 ** self.decimals)
        return v * MM_PER_INCH if self.unit == "inch" else v


class RasterRenderer:
    @staticmethod
    def is_proteus_graphical_drill_layer_name(name: str) -> bool:
        """Proteus graphical drill Gerber / drill legend table layer.

        Proteus exports a normal Excellon file as *.DRL and also a graphical
        Gerber layer named like "... Drill.GBR".  That Drill.GBR contains the
        complete drill legend/table below the PCB.  It must not be clipped
        against the PCB board reference.
        """
        n = name.lower().replace("\\", "/")
        base = n.rsplit("/", 1)[-1]
        return (
            base.endswith(".gbr")
            and "drill" in base
            and not any(k in base for k in ("copper", "mask", "paste", "silk", "solder", "assembly"))
        )

    @staticmethod
    def is_drill_legend_or_table_layer_name(name: str) -> bool:
        """Graphical drill legend/table/report layers that must draw complete."""
        n = name.lower().replace("\\", "/")
        base = n.rsplit("/", 1)[-1]
        if RasterRenderer.is_proteus_graphical_drill_layer_name(name):
            return True
        return any(k in base for k in (
            "read-me", "read_me", "readme",
            "drill drawing", "drill_drawing", "drilldrawing",
            "drill legend", "drill_legend", "drilllegend",
            "drill table", "drill_table", "drilltable",
            "drill chart", "drill_chart", "drillchart",
            "drillmap", "drill-map",
            "ncdrill", "nc drill",
            "plated drill", "non-plated drill",
        )) or base.endswith(".txt") or base.endswith(".drl")

    def __init__(self):
        self.px_per_mm = 36.0
        self.max_side = 7000
        self.margin_px = 80
        self.last_world_bounds = QRectF()
        self.last_px_per_mm = self.px_per_mm

    def layer_bounds(self, layer: Layer) -> QRectF:
        box = QRectF()
        first = True

        def add(r: QRectF):
            nonlocal box, first
            if not r.isValid():
                return
            box = QRectF(r) if first else box.united(r)
            first = False

        for prim in layer.primitives:
            if prim.kind == "line" and len(prim.points) >= 2:
                w = max(prim.width, 0.001)
                add(QRectF(prim.points[0], prim.points[1]).normalized().adjusted(-w, -w, w, w))

            elif prim.kind == "polyline" and len(prim.points) >= 2:
                path = self.cached_polyline_path(prim)
                w = max(prim.width, 0.001)
                add(path.boundingRect().adjusted(-w, -w, w, w))

            elif prim.kind == "region" and prim.contours:
                path = self.cached_region_path(prim)
                add(path.boundingRect())

            elif prim.kind == "circle" and prim.points:
                cpt, r = prim.points[0], max(prim.radius, 0.001)
                add(QRectF(cpt.x() - r, cpt.y() - r, 2*r, 2*r))

            elif prim.kind == "thermal" and prim.points:
                cpt = prim.points[0]
                r = max(float(getattr(prim, "outer_d", 0.0) or 0.0) / 2.0, max(prim.radius, 0.001))
                add(QRectF(cpt.x() - r, cpt.y() - r, 2*r, 2*r))

            elif prim.kind in ("rect", "obround") and prim.points:
                cpt = prim.points[0]
                w, h = prim.rect or (0.2, 0.2)
                add(QRectF(cpt.x() - w/2, cpt.y() - h/2, w, h))

            elif prim.kind == "polygon" and len(prim.points) >= 3:
                poly = QPolygonF(prim.points)
                add(poly.boundingRect())

        return box if not first else QRectF()

    @staticmethod
    def is_helper_camera_layer_name(name: str) -> bool:
        """Layers that are useful as annotations but must not control FIT/bbox.

        Altium exports Drawing/Drillmap/Assembly/3D/Courtyard/Designator layers
        in the same file set, but they often include sheet-origin graphics,
        component origin marks or drill charts. If these layers define the camera,
        the real PCB becomes a tiny object in a huge empty canvas.
        """
        n = name.lower()
        if RasterRenderer.is_drill_legend_or_table_layer_name(n):
            return True
        return any(k in n for k in (
            "drawing", "drillmap", "assembly", "3d_body", "3d",
            "component_center", "component_outline", "courtyard",
            "designator", "roundholes-plated", "slotholes-plated",
            "mechanical_13", "mechanical_15"
        ))

    @staticmethod
    def is_board_camera_layer_name(name: str) -> bool:
        """True only for real PCB fabrication geometry that should define FIT."""
        n = name.lower()
        if RasterRenderer.is_drill_legend_or_table_layer_name(n):
            return False
        if RasterRenderer.is_helper_camera_layer_name(n):
            return False
        if any(k in n for k in ("copper", "signal", "pads", "paste", "soldermask", "mask", "legend", "silk")):
            return True
        if "profile" in n or "mechanical_1" in n:
            return True
        if "pth_drill" in n and n.endswith(".gbr"):
            return True
        return False

    def filtered_layer_bounds(self, layer: Layer, board_ref: Optional[QRectF] = None) -> QRectF:
        """BBox after rejecting per-primitive outliers. Used for camera/FIT only."""
        if board_ref is None or not board_ref.isValid():
            return self.layer_bounds(layer)
        cache = self.layer_bounds_cache(layer)
        box = QRectF()
        first = True
        for pb in cache:
            if not pb.isValid() or pb.width() <= 0 or pb.height() <= 0:
                continue
            if not self.primitive_allowed_bounds(layer, pb, board_ref):
                continue
            box = QRectF(pb) if first else box.united(pb)
            first = False
        return box if not first else QRectF()

    def bounds(self, layers: List[Layer]) -> QRectF:
        visible_boxes = []
        camera_boxes = []
        for layer in layers:
            if not layer.visible:
                continue
            b = self.layer_bounds(layer)
            layer.bbox = b
            if b.isValid() and b.width() > 0 and b.height() > 0:
                nb = b.normalized()
                visible_boxes.append((layer, nb))
                if self.is_board_camera_layer_name(layer.name):
                    camera_boxes.append((layer, nb))

        if not visible_boxes:
            return QRectF(-1, -1, 2, 2)

        if len(visible_boxes) == 1:
            return QRectF(visible_boxes[0][1]).normalized()

        if not camera_boxes:
            box = QRectF()
            first = True
            for _, b in visible_boxes:
                if max(b.width(), b.height()) > 2000.0:
                    continue
                box = QRectF(b) if first else box.united(b)
                first = False
            if not first:
                return box.normalized()
            camera_boxes = visible_boxes

        ref = QRectF(camera_boxes[0][1])
        for _, b in camera_boxes[1:]:
            if max(b.width(), b.height()) < 250.0:
                ref = ref.united(b)

        box = QRectF()
        first = True
        for layer, b in camera_boxes:
            fb = self.filtered_layer_bounds(layer, ref).normalized()
            if not fb.isValid() or fb.width() <= 0 or fb.height() <= 0:
                fb = b

            span = max(fb.width(), fb.height())
            dist = math.hypot(fb.center().x() - ref.center().x(), fb.center().y() - ref.center().y())
            ref_span = max(ref.width(), ref.height(), 1.0)
            if span > max(180.0, ref_span * 3.0):
                continue
            if dist > max(90.0, ref_span * 2.0):
                continue

            box = QRectF(fb) if first else box.united(fb)
            first = False

        if not first:
            for layer, b in visible_boxes:
                if self.is_drill_legend_or_table_layer_name(layer.name):
                    if b.isValid() and b.width() > 0 and b.height() > 0:
                        box = box.united(b.normalized())
            return box

        for layer, b in visible_boxes:
            if self.is_drill_legend_or_table_layer_name(layer.name):
                if b.isValid() and b.width() > 0 and b.height() > 0:
                    ref = ref.united(b.normalized())

        return ref

    def render(self, layers: List[Layer]) -> QImage:
        wb = self.bounds(layers).normalized()
        if wb.width() <= 0 or wb.height() <= 0:
            img = QImage(800, 600, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor(7, 11, 20))
            return img

        px_per_mm = self.px_per_mm
        need_w = wb.width() * px_per_mm + 2 * self.margin_px
        need_h = wb.height() * px_per_mm + 2 * self.margin_px

        if max(need_w, need_h) > self.max_side:
            px_per_mm *= self.max_side / max(need_w, need_h)
            px_per_mm = max(2.0, px_per_mm)

        img_w = max(100, int(math.ceil(wb.width() * px_per_mm + 2 * self.margin_px)))
        img_h = max(100, int(math.ceil(wb.height() * px_per_mm + 2 * self.margin_px)))

        img = QImage(img_w, img_h, QImage.Format.Format_ARGB32_Premultiplied)
        img.fill(QColor(7, 11, 20))

        p = QPainter(img)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)

        p.translate(self.margin_px - wb.left() * px_per_mm, self.margin_px + wb.bottom() * px_per_mm)
        p.scale(px_per_mm, -px_per_mm)

        visible_layers = [l for l in layers if l.visible]
        board_ref = QRectF() if len(visible_layers) == 1 else self.main_board_reference(layers)

        def layer_order(layer: Layer) -> int:
            n = layer.name.lower()
            if "copper" in n or "signal" in n:
                return 10
            if "pads" in n:
                return 20
            if "mask" in n:
                return 30
            if "paste" in n:
                return 35
            if "profile" in n:
                return 50
            if "legend" in n or "silk" in n:
                return 70
            if "drill" in n:
                return 80
            if any(k in n for k in ("assembly", "3d", "component_center", "component_outline", "courtyard", "drawing", "drillmap", "mechanical")):
                return 90
            return 60

        world_transform = p.transform()
        for layer in sorted([l for l in layers if l.visible], key=layer_order):
            layer_img = QImage(img_w, img_h, QImage.Format.Format_ARGB32_Premultiplied)
            layer_img.fill(QColor(0, 0, 0, 0))
            lp = QPainter(layer_img)
            lp.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            lp.setTransform(world_transform)
            self.draw_layer(lp, layer, board_ref)
            lp.end()

            p.save()
            p.resetTransform()
            p.drawImage(0, 0, layer_img)
            p.restore()

        p.end()

        self.last_world_bounds = wb
        self.last_px_per_mm = px_per_mm
        return img


    def primitive_bounds(self, prim: Primitive) -> QRectF:
        if prim.kind == "line" and len(prim.points) >= 2:
            w = max(prim.width, 0.001)
            return QRectF(prim.points[0], prim.points[1]).normalized().adjusted(-w, -w, w, w)

        if prim.kind == "polyline" and len(prim.points) >= 2:
            path = QPainterPath(prim.points[0])
            for pt in prim.points[1:]:
                path.lineTo(pt)
            w = max(prim.width, 0.001)
            return path.boundingRect().adjusted(-w, -w, w, w)

        if prim.kind == "region" and prim.contours:
            return self.region_path(prim).boundingRect()

        if prim.kind == "circle" and prim.points:
            c, r = prim.points[0], max(prim.radius, 0.001)
            return QRectF(c.x() - r, c.y() - r, 2*r, 2*r)

        if prim.kind == "thermal" and prim.points:
            c = prim.points[0]
            r = max(float(getattr(prim, "outer_d", 0.0) or 0.0) / 2.0, max(prim.radius, 0.001))
            return QRectF(c.x() - r, c.y() - r, 2*r, 2*r)

        if prim.kind in ("rect", "obround") and prim.points:
            c = prim.points[0]
            w, h = prim.rect or (0.2, 0.2)
            return QRectF(c.x() - w/2, c.y() - h/2, w, h)

        if prim.kind == "polygon" and len(prim.points) >= 3:
            return QPolygonF(prim.points).boundingRect()

        return QRectF()

    def main_board_reference(self, layers: List[Layer]) -> QRectF:
        candidates = []
        for layer in layers:
            if not layer.visible:
                continue
            if not self.is_board_camera_layer_name(layer.name):
                continue
            b = self.layer_bounds(layer).normalized()
            if not b.isValid() or b.width() <= 0 or b.height() <= 0:
                continue

            lname = layer.name.lower()
            score = 0
            if "copper" in lname or "signal" in lname:
                score = 100
            elif "pads" in lname:
                score = 95
            elif "mask" in lname or "soldermask" in lname:
                score = 85
            elif "paste" in lname:
                score = 70
            elif "legend" in lname or "silk" in lname:
                score = 60
            elif "pth_drill" in lname:
                score = 50

            area = max(b.width() * b.height(), 0.0)
            candidates.append((score, area, b))

        if not candidates:
            for layer in layers:
                if not layer.visible:
                    continue
                b = self.layer_bounds(layer).normalized()
                if b.isValid() and b.width() > 0 and b.height() > 0:
                    candidates.append((10, b.width() * b.height(), b))

        if not candidates:
            return QRectF()

        candidates.sort(key=lambda x: (x[0], x[1]), reverse=True)
        ref = QRectF(candidates[0][2])

        rc = ref.center()
        for score, area, b in candidates[1:]:
            if score < 50:
                continue
            dist = math.hypot(b.center().x() - rc.x(), b.center().y() - rc.y())
            if dist < max(70.0, max(ref.width(), ref.height()) * 1.5) and max(b.width(), b.height()) < 250.0:
                ref = ref.united(b)

        return ref.normalized()

    def primitive_allowed_bounds(self, layer: Layer, pb: QRectF, board_ref: QRectF) -> bool:
        """Fast version of primitive_allowed() using a precomputed primitive bbox."""
        pb = QRectF(pb).normalized()
        if not pb.isValid() or pb.width() <= 0 or pb.height() <= 0:
            return False

        lname = layer.name.lower()

        if self.is_drill_legend_or_table_layer_name(lname):
            return True

        if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
            return True

        expanded = QRectF(board_ref).adjusted(-15, -15, 15, 15)
        strict_layer = any(k in lname for k in (
            "copper", "signal", "pads", "mask", "legend", "silk", "paste", "drill"
        ))
        annotation_layer = any(k in lname for k in (
            "assembly", "3d", "mechanical", "drawing", "drillmap"
        ))

        if expanded.intersects(pb) or expanded.contains(pb.center()):
            return True

        dist = math.hypot(pb.center().x() - board_ref.center().x(), pb.center().y() - board_ref.center().y())
        span = max(pb.width(), pb.height())
        area = pb.width() * pb.height()

        if strict_layer:
            return False
        if annotation_layer and dist > max(40.0, max(board_ref.width(), board_ref.height()) * 0.75) and area < 200.0:
            return False
        if span > max(250.0, max(board_ref.width(), board_ref.height()) * 4.0):
            return False
        return True

    def layer_bounds_cache(self, layer: Layer) -> List[QRectF]:
        """Precompute primitive bboxes once per layer; huge speed gain during vector zoom/pan."""
        cache = getattr(layer, "_fast_bounds_cache", None)
        if cache is None or len(cache) != len(layer.primitives):
            cache = [self.primitive_bounds(prim).normalized() for prim in layer.primitives]
            setattr(layer, "_fast_bounds_cache", cache)
            setattr(layer, "_viewport_candidate_cache", None)
        return cache

    def visible_primitive_indices(self, layer: Layer, view_world: QRectF) -> List[int]:
        """Fast viewport culling with cache quantized to screen movement.

        The old draw loop checked every primitive on every paint.  On heavy
        silk/drill layers this kills pan/zoom performance.  This function
        calculates the visible primitive indices only when the viewport changes
        enough; between tiny mouse moves it reuses the previous list.
        """
        if view_world is None or not view_world.isValid():
            return list(range(len(layer.primitives)))

        cache = self.layer_bounds_cache(layer)
        if not cache:
            return []

        q = 0.15
        key = (
            int(view_world.left() / q),
            int(view_world.top() / q),
            int(view_world.right() / q),
            int(view_world.bottom() / q),
            len(cache),
        )
        old = getattr(layer, "_viewport_candidate_cache", None)
        if old is not None and old[0] == key:
            return old[1]

        vw = QRectF(view_world).adjusted(-0.8, -0.8, 0.8, 0.8)
        indices = [i for i, b in enumerate(cache) if b.isValid() and vw.intersects(b)]

        setattr(layer, "_viewport_candidate_cache", (key, indices))
        return indices

    def cached_polyline_path(self, prim: Primitive) -> QPainterPath:
        path = getattr(prim, "_fast_path_cache", None)
        if path is None:
            path = QPainterPath(prim.points[0])
            for pt in prim.points[1:]:
                path.lineTo(pt)
            setattr(prim, "_fast_path_cache", path)
        return path

    def cached_solid_stroke_path(self, prim: Primitive) -> QPainterPath:
        """Cached filled stroke geometry for KiCad/GerbView-style copper display.

        Drawing each track as a transparent pen creates visible joints/round blobs
        at segment boundaries.  GerbView-style display is cleaner when the D01
        strokes are converted once to filled geometry and painted opaque.
        The cached path also keeps pan/zoom instant.
        """
        cache_key = (prim.kind, round(float(max(prim.width, 0.001)), 6), len(prim.points))
        old_key = getattr(prim, "_solid_stroke_cache_key", None)
        cached = getattr(prim, "_solid_stroke_cache", None)
        if cached is not None and old_key == cache_key:
            return cached

        if prim.kind == "line" and len(prim.points) >= 2:
            base = QPainterPath()
            base.moveTo(prim.points[0])
            base.lineTo(prim.points[1])
        elif prim.kind == "polyline" and len(prim.points) >= 2:
            base = self.cached_polyline_path(prim)
        else:
            return QPainterPath()

        stroker = QPainterPathStroker()
        stroker.setWidth(max(float(prim.width), 0.001))
        stroker.setCapStyle(Qt.PenCapStyle.RoundCap)
        stroker.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
        cached = stroker.createStroke(base)
        setattr(prim, "_solid_stroke_cache", cached)
        setattr(prim, "_solid_stroke_cache_key", cache_key)
        return cached

    def cached_region_path(self, prim: Primitive) -> QPainterPath:
        path = getattr(prim, "_fast_region_path_cache", None)
        if path is None:
            path = self.region_path(prim)
            setattr(prim, "_fast_region_path_cache", path)
        return path

    def cached_polygon(self, prim: Primitive) -> QPolygonF:
        poly = getattr(prim, "_fast_polygon_cache", None)
        if poly is None:
            poly = QPolygonF(prim.points)
            setattr(prim, "_fast_polygon_cache", poly)
        return poly

    def primitive_allowed(self, layer: Layer, prim: Primitive, board_ref: QRectF) -> bool:
        pb = self.primitive_bounds(prim).normalized()
        if not pb.isValid() or pb.width() <= 0 or pb.height() <= 0:
            return False

        lname = layer.name.lower()

        if self.is_drill_legend_or_table_layer_name(lname):
            return True

        if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
            return True

        expanded = QRectF(board_ref).adjusted(-15, -15, 15, 15)

        strict_layer = any(k in lname for k in (
            "copper", "signal", "pads", "mask", "legend", "silk", "paste", "drill"
        ))

        annotation_layer = any(k in lname for k in (
            "assembly", "3d", "mechanical", "drawing", "drillmap"
        ))

        if expanded.intersects(pb) or expanded.contains(pb.center()):
            return True

        dist = math.hypot(pb.center().x() - board_ref.center().x(), pb.center().y() - board_ref.center().y())
        span = max(pb.width(), pb.height())
        area = pb.width() * pb.height()

        if strict_layer:
            return False

        if annotation_layer and dist > max(40.0, max(board_ref.width(), board_ref.height()) * 0.75) and area < 200.0:
            return False

        if span > max(250.0, max(board_ref.width(), board_ref.height()) * 4.0):
            return False

        return True


    @staticmethod
    def is_wireframe_visual_layer_name(name: str) -> bool:
        """Helper/annotation Gerbers must be visible, but not painted as filled copper.

        Altium Assembly / 3D Body / Component Outline / Courtyard / Drawing / Drillmap
        layers are documentation geometry. If their regions/polygons are filled like copper,
        they create the big yellow/orange rectangles the user saw over the PCB. They should
        be rendered as thin vector outlines only.
        """
        n = name.lower()
        return any(k in n for k in (
            "3d_body", "3d", "component_center", "component_outline",
            "courtyard", "drawing", "drillmap"
        )) or ("mechanical" in n and "profile" not in n)

    @staticmethod
    def is_text_hole_layer_name(name: str) -> bool:
        """Layers where old Altium/Protel text may be exported as separate filled polygons.

        Some legacy Altium CAM outputs do not keep the inner loops of letters
        (O, R, B, 8, 6, 9, P, D) inside the same Gerber region.  Instead the
        outer and inner shapes arrive as independent polygons/regions. If each
        primitive is painted separately, the inner holes are filled.  On text
        layers we therefore paint polygon/region text geometry as one
        OddEvenFill film, like CAMtastic/GerbView.
        """
        n = name.lower().replace("\\", "/")
        base = n.rsplit("/", 1)[-1]
        return any(k in n for k in (
            "silk", "legend", "designator", "overlay", "topsilk", "bottomsilk",
            "top_silk", "bottom_silk", "topoverlay", "bottomoverlay",
        )) or base.endswith((".gto", ".gbo", ".sst", ".ssb", ".plc", ".pls"))

    @staticmethod
    def is_fab_filled_layer_name(name: str) -> bool:
        """Real fabrication layers that are allowed to be filled."""
        n = name.lower()
        return any(k in n for k in (
            "copper", "signal", "pads", "paste", "soldermask", "mask",
            "legend", "silk", "pth_drill", "assembly", "mechanical"
        )) and not RasterRenderer.is_wireframe_visual_layer_name(n)

    @staticmethod
    def thermal_relief_polygons(x: float, y: float, outer_d: float, inner_d: float, gap: float, rot_deg: float = 0.0) -> List[List[QPointF]]:
        outer_r = max(abs(outer_d) / 2.0, 1e-6)
        inner_r = max(abs(inner_d) / 2.0, 0.0)
        if inner_r >= outer_r:
            inner_r = outer_r * 0.72
        mean_r = max((outer_r + inner_r) / 2.0, 1e-6)
        gap_ang = max(4.0, min(42.0, math.degrees(abs(gap) / mean_r)))
        half_gap = gap_ang / 2.0
        sectors = []
        for base in (0.0, 90.0, 180.0, 270.0):
            a0 = math.radians(base + half_gap + rot_deg)
            a1 = math.radians(base + 90.0 - half_gap + rot_deg)
            steps = 28
            pts = []
            for k in range(steps + 1):
                a = a0 + (a1 - a0) * k / steps
                pts.append(QPointF(x + outer_r * math.cos(a), y + outer_r * math.sin(a)))
            for k in range(steps, -1, -1):
                a = a0 + (a1 - a0) * k / steps
                pts.append(QPointF(x + inner_r * math.cos(a), y + inner_r * math.sin(a)))
            if len(pts) >= 3:
                sectors.append(pts)
        return sectors


    @staticmethod
    def is_negative_plane_layer(layer: Layer) -> bool:
        """Return True only for explicitly negative-image Gerber layers.

        Important compatibility rule:
        .GP1/.GP2 are often *named* plane layers in Protel/Altium/CAMtastic,
        but the Gerber file itself may already contain positive visual artwork
        (outline, antipads and thermal symbols).  Forcing every .GPx file to a
        filled negative image creates the huge purple rectangle seen in v17.

        Therefore we obey real RS-274X image polarity (IPNEG) or explicit
        negative metadata only.  Plain .GP1/.GP2 are rendered as positive artwork,
        while their THD/Relief aperture macros are still drawn as thermal reliefs.
        """
        name = (getattr(layer, "name", "") or "").lower()
        info = (getattr(layer, "info", "") or "").lower()
        image_pol = str(getattr(layer, "image_polarity", "positive") or "positive").lower()
        if image_pol == "negative":
            return True
        explicit_negative_words = (
            "ipneg", "image polarity: negative", "image_polarity=negative",
            "negative image", "negative plane", "negative polarity"
        )
        if any(k in info for k in explicit_negative_words):
            return True
        if any(k in name for k in ("negative_plane", "negative-image", "negative_image")):
            return True
        return False

    def negative_plane_bounds(self, layer: Layer, board_ref: Optional[QRectF]) -> QRectF:
        """Choose a safe fill extent for negative planes.

        Prefer the board reference/outline if available; otherwise use the layer
        geometry bbox.  The small margin prevents edge-antialias holes but avoids
        huge CAM drawing sheets controlling the fill.
        """
        if board_ref is not None and board_ref.isValid() and board_ref.width() > 0 and board_ref.height() > 0:
            return QRectF(board_ref).adjusted(-0.02, -0.02, 0.02, 0.02).normalized()
        b = self.layer_bounds(layer).normalized()
        if b.isValid() and b.width() > 0 and b.height() > 0:
            return b.adjusted(-0.02, -0.02, 0.02, 0.02).normalized()
        return QRectF()

    def draw_negative_plane_layer(self, p: QPainter, layer: Layer, board_ref: Optional[QRectF], base_color: QColor):
        """Render legacy/internal negative planes as CAM viewers do.

        A negative plane starts as solid copper. Flashes/draws in the file are
        treated as clearances/antipads, while thermal relief macros repaint the
        four copper connections inside the cleared antipad. This fixes old GP1,
        GP2, Protel/Altium/CAMtastic-style planes without changing normal copper,
        mask, paste, silk or drill layers.
        """
        plane_box = self.negative_plane_bounds(layer, board_ref)
        if not plane_box.isValid() or plane_box.width() <= 0 or plane_box.height() <= 0:
            return

        bg = QColor(7, 11, 20, 255)
        copper = QColor(base_color)
        copper.setAlpha(255)
        p.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(copper))
        p.drawRect(plane_box)

        view_world = getattr(self, "current_view_world", None)
        draw_indices = self.visible_primitive_indices(layer, view_world) if view_world is not None and view_world.isValid() else range(len(layer.primitives))
        bounds_cache = self.layer_bounds_cache(layer)

        def draw_clear_for_primitive(prim: Primitive):
            p.setCompositionMode(QPainter.CompositionMode.CompositionMode_Clear)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QBrush(QColor(0, 0, 0, 255)))
            if prim.kind == "circle" and prim.points:
                c, r = prim.points[0], max(float(prim.radius), 0.001)
                p.drawEllipse(c, r, r)
            elif prim.kind == "rect" and prim.points:
                c = prim.points[0]
                w, h = prim.rect or (0.2, 0.2)
                p.drawRect(QRectF(c.x() - w/2, c.y() - h/2, w, h))
            elif prim.kind == "obround" and prim.points:
                c = prim.points[0]
                w, h = prim.rect or (0.2, 0.2)
                rr = QRectF(c.x() - w/2, c.y() - h/2, w, h)
                rad = min(w, h) / 2.0
                p.drawRoundedRect(rr, rad, rad)
            elif prim.kind == "polygon" and len(prim.points) >= 3:
                p.drawPolygon(self.cached_polygon(prim))
            elif prim.kind == "region" and prim.contours:
                p.drawPath(self.cached_region_path(prim))
            elif prim.kind in ("line", "polyline") and len(prim.points) >= 2:
                path = self.cached_solid_stroke_path(prim)
                if not path.isEmpty():
                    p.drawPath(path)

        for idx in draw_indices:
            prim = layer.primitives[idx]
            pb = bounds_cache[idx] if idx < len(bounds_cache) else self.primitive_bounds(prim)
            if (
                not getattr(self, "_export_no_heuristic_filter", False)
                and board_ref is not None and board_ref.isValid()
                and not self.primitive_allowed_bounds(layer, pb, board_ref)
            ):
                continue

            ap_code = str(getattr(prim, "aperture_code", "") or "")
            if prim.kind == "thermal" and prim.points:
                c = prim.points[0]
                od = float(getattr(prim, "outer_d", 0.0) or (prim.radius * 2.0))
                inner = float(getattr(prim, "inner_d", 0.0) or (od * 0.72))
                gap = float(getattr(prim, "gap", 0.0) or (od * 0.11))
                rot = float(getattr(prim, "rotation", 45.0) or 45.0)
                outer_r = max(abs(od) / 2.0, 1e-6)
                inner_r = max(min(abs(inner) / 2.0, outer_r * 0.98), outer_r * 0.15)
                mid_r = (outer_r + inner_r) / 2.0
                ring_w = max(outer_r - inner_r, 0.025)
                gap_ang = max(8.0, min(52.0, math.degrees(abs(gap) / max(mid_r, 1e-6))))

                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_Clear)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QBrush(QColor(0, 0, 0, 255)))
                p.drawEllipse(c, outer_r, outer_r)

                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.setPen(QPen(copper, ring_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.FlatCap, Qt.PenJoinStyle.RoundJoin))
                rr = QRectF(c.x() - mid_r, c.y() - mid_r, 2.0 * mid_r, 2.0 * mid_r)
                for base in (0.0, 90.0, 180.0, 270.0):
                    start = base + rot + gap_ang / 2.0
                    span = 90.0 - gap_ang
                    if span > 1.0:
                        p.drawArc(rr, int(-start * 16), int(-span * 16))
                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_Clear)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QBrush(QColor(0, 0, 0, 255)))
                p.drawEllipse(c, inner_r * 0.55, inner_r * 0.55)
                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
                continue

            if ap_code in {"52", "53"} and prim.points:
                c = prim.points[0]
                if ap_code == "52":
                    od, inner, gap = 0.091496 * MM_PER_INCH, 0.071 * MM_PER_INCH, 0.010 * MM_PER_INCH
                else:
                    od, inner, gap = 0.087559 * MM_PER_INCH, 0.068 * MM_PER_INCH, 0.010 * MM_PER_INCH
                pseudo = Primitive("thermal", points=[c], radius=od / 2.0)
                pseudo.outer_d, pseudo.inner_d, pseudo.gap, pseudo.rotation = od, inner, gap, 45.0
                outer_r, inner_r = od/2.0, inner/2.0
                mid_r, ring_w = (outer_r+inner_r)/2.0, max(outer_r-inner_r, 0.025)
                gap_ang = max(8.0, min(52.0, math.degrees(gap / max(mid_r, 1e-6))))
                p.setPen(Qt.PenStyle.NoPen); p.setBrush(QBrush(bg)); p.drawEllipse(c, outer_r, outer_r)
                p.setBrush(Qt.BrushStyle.NoBrush); p.setPen(QPen(copper, ring_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.FlatCap, Qt.PenJoinStyle.RoundJoin))
                rr = QRectF(c.x()-mid_r, c.y()-mid_r, 2*mid_r, 2*mid_r)
                for base in (0.0, 90.0, 180.0, 270.0):
                    start = base + 45.0 + gap_ang / 2.0
                    span = 90.0 - gap_ang
                    if span > 1.0:
                        p.drawArc(rr, int(-start * 16), int(-span * 16))
                p.setPen(Qt.PenStyle.NoPen); p.setBrush(QBrush(bg)); p.drawEllipse(c, inner_r * 0.55, inner_r * 0.55)
                continue

            draw_clear_for_primitive(prim)

    def primitive_fill_path_for_text_holes(self, prim: Primitive) -> QPainterPath:
        """Return filled geometry for old-Altium text hole reconstruction."""
        path = QPainterPath()
        path.setFillRule(Qt.FillRule.OddEvenFill)

        if prim.kind == "polygon" and len(prim.points) >= 3:
            sub = QPainterPath()
            sub.addPolygon(QPolygonF(prim.points))
            sub.closeSubpath()
            path.addPath(sub)

        elif prim.kind == "region" and prim.contours:
            rp = self.cached_region_path(prim)
            rp.setFillRule(Qt.FillRule.OddEvenFill)
            path.addPath(rp)

        return path

    def draw_layer(self, p: QPainter, layer: Layer, board_ref: Optional[QRectF] = None):
        lname = layer.name.lower()

        base_color = QColor(layer.color)

        if "copper" in lname or "signal" in lname:
            base_color.setAlpha(255)
        elif "pads" in lname:
            base_color.setAlpha(255)
        elif "mask" in lname:
            base_color.setAlpha(90)
        elif "paste" in lname:
            base_color.setAlpha(130)
        elif "legend" in lname or "silk" in lname:
            base_color.setAlpha(245)
        elif self.is_wireframe_visual_layer_name(lname):
            base_color.setAlpha(115)
        elif "mechanical" in lname or "profile" in lname:
            base_color.setAlpha(170)

        typ_meta = str(getattr(layer, "layer_type", "") or "").lower()
        base_color.setAlpha(255)

        if getattr(layer, "legacy_altium_mode", False) and self.is_negative_plane_layer(layer):
            self.draw_negative_plane_layer(p, layer, board_ref, base_color)
            return

        view_world = getattr(self, "current_view_world", None)
        screen_px_per_mm = float(getattr(self, "current_screen_px_per_mm", 0.0) or 0.0)
        lod_px = float(getattr(self, "current_lod_px", 0.0) or 0.0)
        bounds_cache = self.layer_bounds_cache(layer)

        wireframe_visual = self.is_drill_legend_or_table_layer_name(lname)
        typ_meta = str(getattr(layer, "layer_type", "") or "").lower()
        if typ_meta not in {"mask", "paste"}:
            base_color.setAlpha(255)

        single_layer_inspection = board_ref is None or not board_ref.isValid()

        if view_world is not None and view_world.isValid():
            draw_indices = self.visible_primitive_indices(layer, view_world)
        else:
            draw_indices = range(len(layer.primitives))

        # OLD ALTIUM TEXT FIX ONLY:
        # Do not change drill alignment, layer positions, camera, copper or pads.
        # This only fixes filled letters on text/silkscreen/designator layers.
        # Legacy Altium often exports letter holes as separate polygons, so
        # drawing every polygon independently fills O/R/B/8/6/9/P/D.  We combine
        # only polygon/region text geometry into one OddEvenFill path.
        combined_text_path = QPainterPath()
        combined_text_path.setFillRule(Qt.FillRule.OddEvenFill)
        combined_text_indices = set()
        use_combined_text_holes = self.is_text_hole_layer_name(lname) and not wireframe_visual

        if use_combined_text_holes:
            for idx in draw_indices:
                prim = layer.primitives[idx]
                if prim.kind not in {"polygon", "region"}:
                    continue
                pb = bounds_cache[idx] if idx < len(bounds_cache) else self.primitive_bounds(prim)
                if lod_px > 0.0 and pb.isValid():
                    if max(pb.width(), pb.height()) * screen_px_per_mm < lod_px:
                        continue
                if (
                    not getattr(self, "_export_no_heuristic_filter", False)
                    and board_ref is not None
                    and not self.primitive_allowed_bounds(layer, pb, board_ref)
                ):
                    continue
                sub = self.primitive_fill_path_for_text_holes(prim)
                if not sub.isEmpty():
                    combined_text_path.addPath(sub)
                    combined_text_indices.add(idx)

            if not combined_text_path.isEmpty():
                old_mode = p.compositionMode()
                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QBrush(base_color))
                # Keep AA here; text must stay smooth.  OddEvenFill opens the holes.
                p.drawPath(combined_text_path)
                p.setCompositionMode(old_mode)

        for idx in draw_indices:
            if idx in combined_text_indices:
                continue
            prim = layer.primitives[idx]
            pb = bounds_cache[idx] if idx < len(bounds_cache) else self.primitive_bounds(prim)

            if lod_px > 0.0 and pb.isValid():
                if max(pb.width(), pb.height()) * screen_px_per_mm < lod_px:
                    continue
            if (
                not getattr(self, "_export_no_heuristic_filter", False)
                and board_ref is not None
                and not self.primitive_allowed_bounds(layer, pb, board_ref)
            ):
                continue

            is_clear = getattr(prim, "polarity", "dark") == "clear"
            clear_supported = (
                typ_meta in {"copper", "pads", "mask", "soldermask", "paste"}
                or any(k in lname for k in (
                    "copper", "signal", "pads", "mask", "soldermask", "paste",
                    ".gtl", ".gbl", ".g1", ".g2", ".gp1", ".gp2",
                ))
            ) and not wireframe_visual
            if is_clear and not clear_supported:
                continue
            if is_clear:
                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_Clear)
                c = QColor(0, 0, 0, 255)
            else:
                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
                c = QColor(base_color)

            brush = QBrush(c)
            outline_pen_width = 0.055 if wireframe_visual else 0.08

            ap_code = str(getattr(prim, "aperture_code", "") or "")
            if getattr(layer, "legacy_altium_mode", False) and ap_code in {"52", "53"} and prim.points:
                p.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)
                center = prim.points[0]
                if ap_code == "52":
                    od, inner, gap = 0.091496 * MM_PER_INCH, 0.071 * MM_PER_INCH, 0.010 * MM_PER_INCH
                else:
                    od, inner, gap = 0.087559 * MM_PER_INCH, 0.068 * MM_PER_INCH, 0.010 * MM_PER_INCH
                rot = 45.0
                outer_r = od / 2.0
                inner_r = inner / 2.0
                mid_r = (outer_r + inner_r) / 2.0
                ring_w = max(outer_r - inner_r, 0.035)
                gap_ang = max(10.0, min(50.0, math.degrees(gap / max(mid_r, 1e-9))))
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.setPen(QPen(c, ring_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.FlatCap, Qt.PenJoinStyle.RoundJoin))
                rr = QRectF(center.x() - mid_r, center.y() - mid_r, 2.0 * mid_r, 2.0 * mid_r)
                for base_ang in (0.0, 90.0, 180.0, 270.0):
                    start = base_ang + rot + gap_ang / 2.0
                    span = 90.0 - gap_ang
                    if span > 1.0:
                        p.drawArc(rr, int(-start * 16), int(-span * 16))
                continue

            if prim.kind == "line" and len(prim.points) >= 2:
                pen_width = max(prim.width, 0.001)
                fab_solid = True

                if fab_solid and not wireframe_visual:
                    solid_path = self.cached_solid_stroke_path(prim)
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(QBrush(c))
                    p.drawPath(solid_path)
                    if typ_meta == "copper" and not is_clear and (not single_layer_inspection) and bool(getattr(self, "enable_copper_route_accent", False)):
                        route_c = QColor(7, 11, 20, 145)
                        route_w = max(min(float(prim.width) * 0.42, float(prim.width) - 0.001), 0.012)
                        p.setPen(QPen(route_c, route_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                        p.setBrush(Qt.BrushStyle.NoBrush)
                        p.drawLine(prim.points[0], prim.points[1])
                else:
                    if wireframe_visual or "mechanical" in lname or "profile" in lname or "drawing" in lname:
                        pen_width = max(min(prim.width, 0.10), outline_pen_width)
                    pen = QPen(c, pen_width, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
                    p.setPen(pen)
                    p.setBrush(Qt.BrushStyle.NoBrush)
                    p.drawLine(prim.points[0], prim.points[1])

            elif prim.kind == "polyline" and len(prim.points) >= 2:
                path = self.cached_polyline_path(prim)
                pen_width = max(prim.width, 0.001)
                fab_solid = True

                if fab_solid and not wireframe_visual:
                    solid_path = self.cached_solid_stroke_path(prim)
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(QBrush(c))
                    p.drawPath(solid_path)
                    if typ_meta == "copper" and not is_clear and (not single_layer_inspection) and bool(getattr(self, "enable_copper_route_accent", False)):
                        route_c = QColor(7, 11, 20, 145)
                        route_w = max(min(float(prim.width) * 0.42, float(prim.width) - 0.001), 0.012)
                        p.setPen(QPen(route_c, route_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                        p.setBrush(Qt.BrushStyle.NoBrush)
                        p.drawPath(path)
                else:
                    if wireframe_visual or "mechanical" in lname or "profile" in lname or "drawing" in lname:
                        pen_width = max(min(prim.width, 0.10), outline_pen_width)
                    pen = QPen(c, pen_width, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
                    p.setPen(pen)
                    p.setBrush(Qt.BrushStyle.NoBrush)
                    p.drawPath(path)

            elif prim.kind == "region" and prim.contours:
                path = self.cached_region_path(prim)
                if wireframe_visual or "mechanical" in lname or "profile" in lname or "drawing" in lname:
                    p.setPen(QPen(c, outline_pen_width))
                    p.setBrush(Qt.BrushStyle.NoBrush)
                    p.drawPath(path)
                else:
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(brush)
                    if (not is_clear) and typ_meta in {"copper", "pads", "mask", "soldermask", "paste"}:
                        self.draw_filled_area_without_hairline(p, lambda path=path: p.drawPath(path))
                    else:
                        p.drawPath(path)

            elif prim.kind == "thermal" and prim.points:
                center = prim.points[0]
                od = float(getattr(prim, "outer_d", 0.0) or (prim.radius * 2.0))
                inner = float(getattr(prim, "inner_d", 0.0) or (od * 0.72))
                gap = float(getattr(prim, "gap", 0.0) or (od * 0.11))
                rot = float(getattr(prim, "rotation", 45.0) or 45.0)

                outer_r = max(abs(od) / 2.0, 1e-6)
                inner_r = max(min(abs(inner) / 2.0, outer_r * 0.98), outer_r * 0.20)
                mid_r = (outer_r + inner_r) / 2.0
                ring_w = max(outer_r - inner_r, 0.025)
                gap_ang = max(8.0, min(48.0, math.degrees(abs(gap) / max(mid_r, 1e-6))))

                p.setBrush(Qt.BrushStyle.NoBrush)
                p.setPen(QPen(c, ring_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.FlatCap, Qt.PenJoinStyle.RoundJoin))
                rr = QRectF(center.x() - mid_r, center.y() - mid_r, 2.0 * mid_r, 2.0 * mid_r)
                for base in (0.0, 90.0, 180.0, 270.0):
                    start = base + rot + gap_ang / 2.0
                    span = 90.0 - gap_ang
                    if span > 1.0:
                        p.drawArc(rr, int(-start * 16), int(-span * 16))

            elif prim.kind == "circle" and prim.points:
                center, r = prim.points[0], max(prim.radius, 0.001)
                if wireframe_visual:
                    p.setPen(QPen(c, outline_pen_width))
                    p.setBrush(Qt.BrushStyle.NoBrush)
                else:
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(brush)
                p.drawEllipse(center, r, r)

            elif prim.kind == "rect" and prim.points:
                center = prim.points[0]
                w, h = prim.rect or (0.2, 0.2)
                rr = QRectF(center.x() - w/2, center.y() - h/2, w, h)
                if wireframe_visual:
                    p.setPen(QPen(c, outline_pen_width))
                    p.setBrush(Qt.BrushStyle.NoBrush)
                else:
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(brush)
                p.drawRect(rr)

            elif prim.kind == "obround" and prim.points:
                center = prim.points[0]
                w, h = prim.rect or (0.2, 0.2)
                rr = QRectF(center.x() - w/2, center.y() - h/2, w, h)
                if wireframe_visual:
                    p.setPen(QPen(c, outline_pen_width))
                    p.setBrush(Qt.BrushStyle.NoBrush)
                else:
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(brush)
                p.drawRoundedRect(rr, min(w, h)/2, min(w, h)/2)

            elif prim.kind == "polygon" and len(prim.points) >= 3:
                poly = self.cached_polygon(prim)
                if wireframe_visual:
                    p.setPen(QPen(c, outline_pen_width))
                    p.setBrush(Qt.BrushStyle.NoBrush)
                    p.drawPolygon(poly, Qt.FillRule.OddEvenFill)
                else:
                    p.setPen(Qt.PenStyle.NoPen)
                    p.setBrush(brush)
                    if (not is_clear) and typ_meta in {"copper", "pads", "mask", "soldermask", "paste"}:
                        self.draw_filled_area_without_hairline(p, lambda poly=poly: p.drawPolygon(poly, Qt.FillRule.OddEvenFill))
                    else:
                        p.drawPolygon(poly, Qt.FillRule.OddEvenFill)

            if (not is_clear) and self.should_draw_dcode_labels(layer, single_layer_inspection):
                if prim.kind != "thermal" and str(getattr(prim, "aperture_code", "") or "") not in {"52", "53"}:
                    self.draw_dcode_label(p, prim, pb, base_color)


    def draw_filled_area_without_hairline(self, p: QPainter, draw_fn):
        """Draw adjacent KiCad zone fragments without anti-aliased hairline seams.

        KiCad 9/10 can fracture copper zones into many region/polygon islands.
        If every island is filled with antialiasing enabled, QPainter blends the
        shared edges with transparency and a tiny false line appears inside a
        solid copper pour.  GerbView treats the copper as one opaque film, so for
        solid filled fabrication areas we temporarily disable AA only for the fill.
        Tracks, pads, circles and outline strokes keep normal antialiasing.
        """
        old_aa = bool(p.testRenderHint(QPainter.RenderHint.Antialiasing))
        if old_aa:
            p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
        draw_fn()
        if old_aa:
            p.setRenderHint(QPainter.RenderHint.Antialiasing, True)


    def should_draw_dcode_labels(self, layer: Layer, single_layer_inspection: bool) -> bool:
        """D-code text overlay disabled.

        Keep aperture_code metadata in primitives for debugging/export, but never
        draw Dxx labels on the canvas. This preserves all working geometry while
        removing the visual clutter over pads/tracks.
        """
        return False

    def draw_dcode_label(self, p: QPainter, prim: Primitive, pb: QRectF, color: QColor):
        code = str(getattr(prim, "aperture_code", "") or "")
        if not code or not pb.isValid():
            return
        span = max(pb.width(), pb.height())
        if span < 0.42:
            return
        center = pb.center()
        text = "D" + code
        p.save()
        p.translate(center.x(), center.y())
        p.scale(1.0, -1.0)
        tc = QColor(color)
        tc.setAlpha(245)
        p.setPen(QPen(tc, 0.018))
        p.setBrush(Qt.BrushStyle.NoBrush)
        font = QFont("Consolas")
        font.setPointSizeF(0.42)
        font.setBold(True)
        path = QPainterPath()
        path.addText(QPointF(-0.28 * len(text), 0.15), font, text)
        p.drawPath(path)
        p.restore()


    @staticmethod
    def region_path(prim: Primitive) -> QPainterPath:
        path = QPainterPath()
        path.setFillRule(Qt.FillRule.OddEvenFill)
        if not prim.contours:
            return path
        for contour in prim.contours:
            if len(contour) < 3:
                continue
            sub = QPainterPath()
            sub.addPolygon(QPolygonF(contour))
            sub.closeSubpath()
            path.addPath(sub)
        return path


    @staticmethod
    def realistic_layer_role(layer: Layer) -> str:
        """Robust layer role for TOP/BOTTOM PNG export.

        This uses the already-classified layer_type when available and then falls
        back to conservative KiCad/Altium/Proteus filename rules.  Drill legends
        and documentation Gerbers are intentionally not treated as real drill
        holes, because they destroy the export bbox and clip the real PCB.
        """
        lt = str(getattr(layer, "layer_type", "") or "").lower().strip()
        if lt in {"copper", "mask", "paste", "silk", "mechanical", "drill", "pads"}:
            return "copper" if lt == "pads" else lt

        n = (str(layer.name) + " " + str(layer.path)).lower().replace("-", "_")
        ext = Path(str(layer.path or layer.name)).suffix.lower()
        base = Path(str(layer.path or layer.name)).name.lower().replace("-", "_")

        if any(k in base for k in ("drill_legend", "drilltable", "drill_table", "drill_chart", "drillmap", "readme")):
            return "other"
        if ext in DRILL_EXTS or any(k in n for k in (".drl", "ncdrill", "pth_drill", "npth_drill", "plated_drill", "non_plated_drill")):
            return "drill"
        if any(k in n for k in ("edge_cuts", "edgecuts", "profile", "board_outline", "outline", "dimension", ".gko", ".gm1", ".gml")):
            return "mechanical"
        if any(k in n for k in ("f_cu", "b_cu", "gtl", "gbl", "top_copper", "bottom_copper", "toplayer", "bottomlayer", "copper", "signal")):
            return "copper"
        if any(k in n for k in ("f_mask", "b_mask", "gts", "gbs", "soldermask", "solder_mask", "resist", "mask")):
            return "mask"
        if any(k in n for k in ("f_paste", "b_paste", "gtp", "gbp", "paste")):
            return "paste"
        if any(k in n for k in ("f_silk", "b_silk", "f_silkscreen", "b_silkscreen", "gto", "gbo", "silk", "legend", "overlay")):
            return "silk"
        return "other"

    @staticmethod
    def realistic_layer_side(layer: Layer) -> str:
        """Return top/bottom/inner/both for physical side export filtering."""
        meta = str(getattr(layer, "layer_side", "") or "").lower().strip()
        if meta in {"top", "bottom", "inner", "both"}:
            return meta

        raw = (str(layer.name) + " " + str(layer.path)).lower().replace("-", "_")
        ext = Path(str(layer.path or layer.name)).suffix.lower()
        if ext in {".gtl", ".gto", ".gts", ".gtp", ".sol", ".cmp", ".stc", ".sts", ".plc", ".smt", ".sst", ".spt"}:
            return "top"
        if ext in {".gbl", ".gbo", ".gbs", ".gbp", ".bot", ".crc", ".crs", ".pls", ".smb", ".ssb", ".spb"}:
            return "bottom"
        if ext in {".gko", ".gm1", ".gm2", ".gm3", ".gm4", ".gml", ".oln", ".dim", ".out", ".fab"} or ext in DRILL_EXTS:
            return "both"
        if re.search(r"(^|[_./\\])f_(cu|mask|paste|silk|silkscreen)([_./\\]|$)", raw):
            return "top"
        if re.search(r"(^|[_./\\])b_(cu|mask|paste|silk|silkscreen)([_./\\]|$)", raw):
            return "bottom"
        if re.search(r"(^|[_./\\])in\d+_cu([_./\\]|$)", raw):
            return "inner"
        if any(k in raw for k in ("bottom", "bot", "back", "b.cu", "b_cu", "kbottom", "gbl", "gbs", "gbp", "gbo", "bottomlayer")):
            return "bottom"
        if any(k in raw for k in ("top", "front", "f.cu", "f_cu", "ktop", "gtl", "gts", "gtp", "gto", "toplayer")):
            return "top"
        return "both"

    def realistic_side_visible(self, layers: List[Layer], side: str = "top") -> List[Layer]:
        """Return the physical layers that belong to one PNG side.

        This no longer trusts the current GUI visibility for explicit TOP/BOTTOM
        export.  The export action must read the actual loaded CAM set and build
        the side composition itself; otherwise a hidden Edge.Cuts/mask/copper layer
        can collapse the PNG to only a few pads.
        """
        side = (side or "top").lower()
        out = []
        allowed_roles = {"copper", "mask", "paste", "silk", "mechanical", "drill"}
        for layer in layers:
            role = self.realistic_layer_role(layer)
            if role not in allowed_roles:
                continue
            ls = self.realistic_layer_side(layer)
            if role in {"drill", "mechanical"} or ls in {"both", side}:
                out.append(layer)
        return out

    def auto_realistic_png_side(self, layers: List[Layer]) -> str:
        """Choose TOP/BOTTOM for realistic PNG from the current visible selection.

        If the user has enabled mostly bottom fabrication layers, export the bottom
        side.  Otherwise default to top.  Drill and Edge.Cuts are neutral.
        """
        score = {"top": 0, "bottom": 0}
        weight_by_role = {"copper": 5, "mask": 3, "paste": 3, "silk": 2}
        for layer in layers:
            if not layer.visible:
                continue
            role = self.realistic_layer_role(layer)
            side = self.realistic_layer_side(layer)
            w = weight_by_role.get(role, 0)
            if side in score:
                score[side] += w
        return "bottom" if score["bottom"] > score["top"] else "top"

    @staticmethod
    def is_board_outline_layer(layer: Layer) -> bool:
        """True for real board contour layers used to cut the realistic PNG body."""
        n = (str(layer.name) + " " + str(layer.path)).lower().replace("-", "_")
        ff = str(getattr(layer, "file_function", "") or "").lower().replace(" ", "")
        if "profile" in ff:
            return True
        return any(k in n for k in (
            "edge_cuts", "edgecuts", "edge.cuts", "profile", "board_outline",
            "boardoutline", "outline", "dimension", "gm1", "gko", "gml"
        ))

    def edge_cut_board_path(self, layers: List[Layer], board_ref: QRectF) -> QPainterPath:
        """Build the real PCB body from Edge.Cuts/Profile/board outline Gerbers.

        This is used only by realistic PNG export.  It deliberately scans all
        loaded layers, not only the currently visible ones, because the board
        material must follow the physical outline even when Edge.Cuts is hidden.
        It supports closed regions/polygons, circular outlines and chained line
        or arc/polyline contours.  Only if no usable contour exists does it fall
        back to a rounded rectangle around the production bbox.
        """
        def add_poly_to_path(dst: QPainterPath, pts: List[QPointF]) -> None:
            if len(pts) < 3:
                return
            dst.moveTo(pts[0])
            for pt in pts[1:]:
                dst.lineTo(pt)
            dst.closeSubpath()

        outline_layers = [layer for layer in layers if self.is_board_outline_layer(layer)]
        if not outline_layers:
            outline_layers = [layer for layer in layers if self.realistic_layer_role(layer) == "mechanical" and self.is_board_outline_layer(layer)]

        path = QPainterPath()
        path.setFillRule(Qt.FillRule.OddEvenFill)
        segments: List[Tuple[QPointF, QPointF]] = []
        outline_bbox = QRectF()
        outline_bbox_first = True

        for layer in outline_layers:
            lb = self.layer_bounds(layer).normalized()
            if lb.isValid() and lb.width() > 0 and lb.height() > 0 and max(lb.width(), lb.height()) < 1000.0:
                outline_bbox = QRectF(lb) if outline_bbox_first else outline_bbox.united(lb)
                outline_bbox_first = False
            for prim in layer.primitives:
                pb = self.primitive_bounds(prim).normalized()
                if not pb.isValid() or pb.width() <= 0 or pb.height() <= 0:
                    continue
                if board_ref.isValid() and max(pb.width(), pb.height()) > max(board_ref.width(), board_ref.height(), 1.0) * 6.0:
                    continue

                if prim.kind == "region" and prim.contours:
                    rp = self.cached_region_path(prim)
                    if rp.boundingRect().isValid():
                        path.addPath(rp)

                elif prim.kind == "polygon" and len(prim.points) >= 3:
                    pp = QPainterPath()
                    pp.setFillRule(Qt.FillRule.OddEvenFill)
                    add_poly_to_path(pp, list(prim.points))
                    path.addPath(pp)

                elif prim.kind == "circle" and prim.points:
                    cpt = prim.points[0]
                    r = max(float(prim.radius), 0.001)
                    path.addEllipse(cpt, r, r)

                elif prim.kind == "rect" and prim.points:
                    cpt = prim.points[0]
                    w, h = prim.rect or (0.2, 0.2)
                    path.addRect(QRectF(cpt.x() - w / 2, cpt.y() - h / 2, w, h))

                elif prim.kind == "obround" and prim.points:
                    cpt = prim.points[0]
                    w, h = prim.rect or (0.2, 0.2)
                    rr = QRectF(cpt.x() - w / 2, cpt.y() - h / 2, w, h)
                    radius = min(abs(w), abs(h)) / 2.0
                    path.addRoundedRect(rr, radius, radius)

                elif prim.kind == "line" and len(prim.points) >= 2:
                    segments.append((prim.points[0], prim.points[1]))

                elif prim.kind == "polyline" and len(prim.points) >= 2:
                    pts = list(prim.points)
                    if len(pts) >= 3 and math.hypot(pts[0].x() - pts[-1].x(), pts[0].y() - pts[-1].y()) <= 0.08:
                        pp = QPainterPath()
                        pp.setFillRule(Qt.FillRule.OddEvenFill)
                        add_poly_to_path(pp, pts)
                        path.addPath(pp)
                    else:
                        for a, b in zip(pts[:-1], pts[1:]):
                            segments.append((a, b))

        if path.boundingRect().isValid() and path.boundingRect().width() > 1 and path.boundingRect().height() > 1:
            return path.simplified()

        # KiCad/GerbView style board body reconstruction:
        # Edge_Cuts is stroke geometry, but the PNG body must be the AREA enclosed
        # by those strokes.  Never use the Edge_Cuts bbox as the final body unless
        # there are truly no usable segments.  A bbox fallback is exactly what makes
        # the soldermask continue outside the real outline.
        ref_span = max(board_ref.width(), board_ref.height(), outline_bbox.width(), outline_bbox.height(), 1.0)
        tol = max(0.08, min(0.75, ref_span * 0.006))

        def close(a: QPointF, b: QPointF) -> bool:
            return math.hypot(a.x() - b.x(), a.y() - b.y()) <= tol

        def signed_area(pts: List[QPointF]) -> float:
            if len(pts) < 3:
                return 0.0
            area = 0.0
            for a, b in zip(pts, pts[1:] + pts[:1]):
                area += a.x() * b.y() - b.x() * a.y()
            return area / 2.0

        def chain_to_path(chain: List[QPointF], force_close: bool = False) -> Optional[QPainterPath]:
            if len(chain) < 3:
                return None
            pts = list(chain)
            if not close(pts[0], pts[-1]):
                if not force_close:
                    return None
                pts.append(QPointF(pts[0]))
            if abs(signed_area(pts[:-1] if close(pts[0], pts[-1]) else pts)) < 0.5:
                return None
            cp = QPainterPath()
            cp.setFillRule(Qt.FillRule.OddEvenFill)
            add_poly_to_path(cp, pts)
            return cp

        closed_paths: List[QPainterPath] = []
        open_chains: List[List[QPointF]] = []
        remaining = list(segments)
        while remaining:
            start, end = remaining.pop(0)
            chain = [start, end]
            changed = True
            while changed and remaining:
                changed = False
                best_i = -1
                best_mode = 0
                best_dist = 1e99
                for i, (a, b) in enumerate(remaining):
                    tests = (
                        (math.hypot(chain[-1].x() - a.x(), chain[-1].y() - a.y()), 1),
                        (math.hypot(chain[-1].x() - b.x(), chain[-1].y() - b.y()), 2),
                        (math.hypot(chain[0].x() - b.x(), chain[0].y() - b.y()), 3),
                        (math.hypot(chain[0].x() - a.x(), chain[0].y() - a.y()), 4),
                    )
                    d, mode = min(tests, key=lambda x: x[0])
                    if d < best_dist:
                        best_dist, best_i, best_mode = d, i, mode
                if best_i >= 0 and best_dist <= tol:
                    a, b = remaining.pop(best_i)
                    if best_mode == 1:
                        chain.append(b)
                    elif best_mode == 2:
                        chain.append(a)
                    elif best_mode == 3:
                        chain.insert(0, a)
                    elif best_mode == 4:
                        chain.insert(0, b)
                    changed = True

            cp = chain_to_path(chain, force_close=False)
            if cp is not None:
                closed_paths.append(cp)
            else:
                open_chains.append(chain)

        # If the outline is almost closed but has a tiny CAD gap, force-close only
        # large chains.  This still rejects small dimension arrows/text on Edge_Cuts.
        if not closed_paths and open_chains:
            ref_area = max(board_ref.width() * board_ref.height(), outline_bbox.width() * outline_bbox.height(), 1.0)
            candidates = []
            for chain in open_chains:
                cp = chain_to_path(chain, force_close=True)
                if cp is None:
                    continue
                br = cp.boundingRect().normalized()
                area = br.width() * br.height()
                poly_area = abs(signed_area(chain))
                if area >= ref_area * 0.20 and poly_area >= ref_area * 0.10:
                    candidates.append((poly_area, area, cp))
            if candidates:
                candidates.sort(key=lambda x: (x[0], x[1]), reverse=True)
                closed_paths.append(candidates[0][2])

        if closed_paths:
            closed_paths.sort(key=lambda pp: pp.boundingRect().width() * pp.boundingRect().height(), reverse=True)
            out = QPainterPath()
            out.setFillRule(Qt.FillRule.OddEvenFill)
            for pp in closed_paths:
                out.addPath(pp)
            return out.simplified()

        # Last resort only: no usable Edge_Cuts contour at all.
        r = QRectF(outline_bbox if (outline_bbox.isValid() and outline_bbox.width() > 0 and outline_bbox.height() > 0) else board_ref).normalized()
        fallback = QPainterPath()
        fallback.setFillRule(Qt.FillRule.OddEvenFill)
        fallback.addRect(r)
        return fallback

    def path_bounds_or_ref(self, path: QPainterPath, ref: QRectF) -> QRectF:
        b = path.boundingRect().normalized()
        return b if b.isValid() and b.width() > 0 and b.height() > 0 else QRectF(ref).normalized()

    def export_production_bounds(self, layers: List[Layer]) -> QRectF:
        """BBox for the real PCB side, excluding legends/tables/helper junk.

        CRITICAL RULE for KiCad/Gerber side PNG export:
        Edge.Cuts / Profile / BoardOutline is the PCB program outline and must
        define the export camera when it exists.  Copper/mask/silk are artwork
        inside that outline; they must not shrink the PNG to a connector/pad
        cluster.  Drill legends, assembly drawings and mechanical documentation
        are still ignored.
        """
        def union_layers(predicate) -> QRectF:
            box = QRectF()
            first = True
            for layer in layers:
                if not predicate(layer):
                    continue
                lname = (str(layer.name) + " " + str(layer.path)).lower()
                if self.is_drill_legend_or_table_layer_name(lname):
                    continue
                b = self.layer_bounds(layer).normalized()
                if not b.isValid() or b.width() <= 0 or b.height() <= 0:
                    continue
                # Real PCBs here are normal-size. Reject CAM sheets/tables, not outlines.
                if max(b.width(), b.height()) > 1000.0:
                    continue
                box = QRectF(b) if first else box.united(b)
                first = False
            return box.normalized() if not first else QRectF()

        # 1) Absolute priority: board outline layer. In KiCad this is Edge_Cuts.gbr
        #    with TF.FileFunction/Profile,NP. This is the correct PCB extent.
        outline_box = union_layers(lambda l: self.is_board_outline_layer(l) or "profile" in str(getattr(l, "file_function", "")).lower())
        if outline_box.isValid() and outline_box.width() > 0 and outline_box.height() > 0:
            return outline_box

        preferred_roles = {"copper", "mask", "paste", "silk"}
        shared_roles = {"mechanical", "drill"}

        def usable_fab_layer(layer: Layer, roles: set[str]) -> bool:
            role = self.realistic_layer_role(layer)
            if role not in roles:
                return False
            lname = (str(layer.name) + " " + str(layer.path)).lower()
            if self.is_wireframe_visual_layer_name(lname) and not self.is_board_outline_layer(layer):
                return False
            return True

        # 2) If there is no outline, use production artwork.
        box = union_layers(lambda l: usable_fab_layer(l, preferred_roles))
        if box.isValid() and box.width() > 0 and box.height() > 0:
            return box

        # 3) Last fallback: include mechanical/drill, but still no legend/table junk.
        return union_layers(lambda l: usable_fab_layer(l, preferred_roles | shared_roles))

    def safe_realistic_body(self, layers: List[Layer], production_ref: QRectF) -> QPainterPath:
        """Build the PCB body for PNG export without letting a broken outline shrink it.

        Edge.Cuts/Profile defines the PCB extent.  Some KiCad/old-CAD outline
        files contain open chains, arcs, or tiny helper flashes; if those cannot
        be reconstructed as a real closed board path, the exporter must NOT clip
        the PCB down to a connector/pad cluster.  In that case we use the
        Edge.Cuts/Profile bounding box as the safe physical board extent.
        """
        ref = QRectF(production_ref).normalized()
        body = self.edge_cut_board_path(layers, ref)
        bb = body.boundingRect().normalized()

        ref_area = max(ref.width() * ref.height(), 1e-9) if ref.isValid() else 0.0
        bb_area = max(bb.width() * bb.height(), 0.0) if bb.isValid() else 0.0

        # Accept a real outline only when it is comparable with the production
        # reference.  A tiny path here is almost always a bad Edge.Cuts parse and
        # causes the exact failure seen by the user: only a few pads exported.
        if (
            bb.isValid() and bb.width() > 1.0 and bb.height() > 1.0
            and ref.isValid() and ref.width() > 0 and ref.height() > 0
            and bb_area >= ref_area * 0.55
        ):
            return body

        fallback = QPainterPath()
        fallback.setFillRule(Qt.FillRule.OddEvenFill)
        fallback.addRect(ref)
        return fallback

    def render_realistic(self, layers: List[Layer], side: str = "top") -> QImage:
        """Realistic PNG export generated from Gerber/Excellon primitives."""
        visible = self.realistic_side_visible(layers, side)
        if not visible:
            img = QImage(800, 600, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor(0, 0, 0))
            return img

        # Build export camera from real side fabrication layers only.
        # Do not let GUI visibility, drill legends, assembly drawings or helper
        # rectangles define the PNG size.
        board_ref = self.export_production_bounds(visible).normalized()
        if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
            old_vis = [(l, l.visible) for l in layers]
            try:
                allowed = set(id(l) for l in visible)
                for l in layers:
                    l.visible = id(l) in allowed
                board_ref = self.main_board_reference(layers).normalized()
                if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
                    board_ref = self.bounds(layers).normalized()
            finally:
                for l, v in old_vis:
                    l.visible = v

        body = self.safe_realistic_body(layers, board_ref)
        body_bounds = self.path_bounds_or_ref(body, board_ref)
        # HARD RULE for TOP/BOTTOM PNG: the physical PCB ends at Edge.Cuts.
        # Do not extend the export camera outside the board outline, even if
        # copper/silk/mechanical artwork exists out there.
        wb = body_bounds.normalized()

        if wb.width() <= 0 or wb.height() <= 0:
            img = QImage(800, 600, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor(0, 0, 0))
            return img

        px_per_mm = self.px_per_mm
        need_w = wb.width() * px_per_mm + 2 * self.margin_px
        need_h = wb.height() * px_per_mm + 2 * self.margin_px
        if max(need_w, need_h) > self.max_side:
            px_per_mm *= self.max_side / max(need_w, need_h)
            px_per_mm = max(2.0, px_per_mm)

        img_w = max(100, int(math.ceil(wb.width() * px_per_mm + 2 * self.margin_px)))
        img_h = max(100, int(math.ceil(wb.height() * px_per_mm + 2 * self.margin_px)))
        img = QImage(img_w, img_h, QImage.Format.Format_ARGB32_Premultiplied)
        img.fill(REALISTIC_BG)

        p = QPainter(img)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)

        # TOP/BOTTOM EXPORT ORIENTATION FIX
        # Keep all parsed Gerber/Excellon primitives in canonical CAM coordinates.
        # For BOTTOM PNG, mirror exactly once at the painter/world transform level.
        # Do NOT mirror the final QImage and do NOT alter primitive coordinates.
        export_side = (side or "top").strip().lower()
        if export_side in ("bottom", "bot", "b", "kbottom", "kicad_bottom", "b.cu"):
            p.translate(self.margin_px + wb.right() * px_per_mm, self.margin_px + wb.bottom() * px_per_mm)
            p.scale(-px_per_mm, -px_per_mm)
        else:
            p.translate(self.margin_px - wb.left() * px_per_mm, self.margin_px + wb.bottom() * px_per_mm)
            p.scale(px_per_mm, -px_per_mm)

        # Pseudo-3D board thickness.  In a top/bottom PNG there is no real camera
        # perspective, so we draw a controlled 1.5 mm offset skirt behind the PCB
        # body.  This gives the same visible board-thickness impression as the
        # supplied reference images without changing the true Gerber coordinates.
        export_side = (side or "top").strip().lower()
        is_bottom_export = export_side in ("bottom", "bot", "b", "kbottom", "kicad_bottom", "b.cu")
        thickness_mm = PCB_THICKNESS_MM
        skirt_dx = thickness_mm * (0.32 if not is_bottom_export else -0.32)
        skirt_dy = -thickness_mm * 0.42
        p.save()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(QColor(0, 0, 0, 95)))
        p.translate(skirt_dx * 1.55, skirt_dy * 1.55)
        p.drawPath(body)
        p.restore()

        p.save()
        p.setPen(Qt.PenStyle.NoPen)
        side_grad = QLinearGradient(QPointF(wb.left(), wb.top()), QPointF(wb.left(), wb.bottom()))
        side_grad.setColorAt(0.0, REALISTIC_EDGE_SIDE)
        side_grad.setColorAt(1.0, REALISTIC_EDGE_SIDE_DARK)
        p.setBrush(QBrush(side_grad))
        p.translate(skirt_dx, skirt_dy)
        p.drawPath(body)
        p.restore()

        p.setClipPath(body)
        p.setPen(Qt.PenStyle.NoPen)

        # Fabrication-style material palette.  The main board is matte soldermask;
        # copper traces/pours remain green under mask, while compact exposed flashes
        # are overpainted as ENIG/gold pads/vias below.
        if is_bottom_export:
            mask_light, mask_mid, mask_dark = REALISTIC_BOTTOM_MASK_LIGHT, REALISTIC_BOTTOM_MASK_MID, REALISTIC_BOTTOM_MASK_DARK
        else:
            mask_light, mask_mid, mask_dark = REALISTIC_TOP_MASK_LIGHT, REALISTIC_TOP_MASK_MID, REALISTIC_TOP_MASK_DARK

        board_grad = QLinearGradient(QPointF(wb.left(), wb.top()), QPointF(wb.right(), wb.bottom()))
        board_grad.setColorAt(0.00, mask_light)
        board_grad.setColorAt(0.45, mask_mid)
        board_grad.setColorAt(1.00, mask_dark)
        p.setBrush(QBrush(board_grad))
        p.drawPath(body)

        # Very soft mask sheen, clipped to the PCB body.
        sheen = QLinearGradient(QPointF(wb.left(), wb.bottom()), QPointF(wb.right(), wb.top()))
        sheen.setColorAt(0.0, QColor(255, 255, 255, 18))
        sheen.setColorAt(0.55, QColor(255, 255, 255, 0))
        sheen.setColorAt(1.0, QColor(0, 0, 0, 32))
        p.setBrush(QBrush(sheen))
        p.drawPath(body)

        copper_bright = REALISTIC_COPPER_TRACE
        pad_gold = REALISTIC_GOLD_MID

        old = [(l, QColor(l.color), l.visible) for l in layers]
        old_export_no_filter = getattr(self, "_export_no_heuristic_filter", False)
        self._export_no_heuristic_filter = True
        try:
            allowed = set(id(l) for l in visible)
            for l in layers:
                l.visible = id(l) in allowed

            def draw_roles(roles, color):
                for layer in visible:
                    if self.realistic_layer_role(layer) in roles:
                        layer.color = QColor(color)
                        self.draw_layer(p, layer, board_ref)

            draw_roles({"copper"}, copper_bright)
            pad_specs = self.draw_realistic_copper_flashes(p, visible, board_ref, pad_gold)
            draw_roles({"paste"}, pad_gold)
            draw_roles({"silk"}, QColor(245, 255, 238, 255))
            self.draw_realistic_drill_holes(p, visible, board_ref, pad_specs)
        finally:
            self._export_no_heuristic_filter = old_export_no_filter
            for layer, col, vis in old:
                layer.color = col
                layer.visible = vis

        p.setClipping(False)
        # Thin light bevel on the board outline, matching the reference renders.
        p.setPen(QPen(REALISTIC_EDGE_LIGHT, 0.075))
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawPath(body)
        p.setPen(QPen(QColor(0, 55, 0, 180), 0.035))
        p.drawPath(body)
        p.end()
        self.last_world_bounds = wb
        self.last_px_per_mm = px_per_mm
        return img

    def render_monochrome(self, layers: List[Layer]) -> QImage:
        """Black/white PDF source: visible user selection only, no realistic colors."""
        if not any(l.visible for l in layers):
            img = QImage(800, 600, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor(255, 255, 255))
            return img
        wb = self.bounds(layers).normalized()
        px_per_mm = self.px_per_mm
        if wb.width() <= 0 or wb.height() <= 0:
            wb = QRectF(-1, -1, 2, 2)
        need_w = wb.width() * px_per_mm + 2 * self.margin_px
        need_h = wb.height() * px_per_mm + 2 * self.margin_px
        if max(need_w, need_h) > self.max_side:
            px_per_mm *= self.max_side / max(need_w, need_h)
            px_per_mm = max(2.0, px_per_mm)
        img_w = max(100, int(math.ceil(wb.width() * px_per_mm + 2 * self.margin_px)))
        img_h = max(100, int(math.ceil(wb.height() * px_per_mm + 2 * self.margin_px)))
        img = QImage(img_w, img_h, QImage.Format.Format_ARGB32_Premultiplied)
        img.fill(QColor(255, 255, 255, 255))
        p = QPainter(img)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.translate(self.margin_px - wb.left() * px_per_mm, self.margin_px + wb.bottom() * px_per_mm)
        p.scale(px_per_mm, -px_per_mm)
        board_ref = self.main_board_reference(layers).normalized()
        old = [(l, QColor(l.color)) for l in layers if l.visible]
        try:
            for l in layers:
                if l.visible:
                    l.color = QColor(0, 0, 0, 255)
                    self.draw_layer(p, l, board_ref)
        finally:
            for l, c in old:
                l.color = c
        p.end()
        self.last_world_bounds = wb
        self.last_px_per_mm = px_per_mm
        return img

    def draw_realistic_copper_flashes(self, p: QPainter, layers: List[Layer], board_ref: QRectF, color: QColor):
        """Paint realistic copper pads without adding fake round 'ears'.

        v25 fix:
        Some CAD exports, especially old macro-based square TH pads, describe a
        square pad as a body plus four small circular/round corner primitives.
        In the realistic PNG export those corner primitives were painted gold
        on top of the pad and looked like unwanted "ears".

        The export now normalizes small square/rectangular pad flashes to a
        clean rectangle and suppresses only the tiny corner-helper circles that
        belong to the same pad. Normal round pads/vias are not affected.
        """
        p.setPen(Qt.PenStyle.NoPen)

        def gold_brush_for_rect(rr: QRectF) -> QBrush:
            rr = QRectF(rr).normalized()
            c = rr.center()
            radius = max(rr.width(), rr.height()) * 0.72
            grad = QRadialGradient(c, max(radius, 0.001), QPointF(c.x() - rr.width() * 0.22, c.y() + rr.height() * 0.22))
            grad.setColorAt(0.00, REALISTIC_GOLD_LIGHT)
            grad.setColorAt(0.50, REALISTIC_GOLD_MID)
            grad.setColorAt(1.00, REALISTIC_GOLD_DARK)
            return QBrush(grad)

        def set_gold_for_circle(c: QPointF, r: float):
            rr = QRectF(c.x() - r, c.y() - r, 2.0 * r, 2.0 * r)
            p.setBrush(gold_brush_for_rect(rr))

        def set_gold_for_rect(rr: QRectF):
            p.setBrush(gold_brush_for_rect(rr))

        # pad_specs entries:
        #   (cx, cy, equivalent_radius, shape, width, height)
        pad_specs = []
        rect_candidates = []  # (cx, cy, w, h, QRectF)

        def allowed(layer: Layer, prim: Primitive) -> bool:
            if getattr(self, "_export_no_heuristic_filter", False):
                return True
            pb = self.primitive_bounds(prim)
            return not (board_ref.isValid() and not self.primitive_allowed_bounds(layer, pb, board_ref))

        def remember_pad(cx: float, cy: float, r: float, shape: str = "round", w: float = 0.0, h: float = 0.0):
            if r > 0.025:
                pad_specs.append((float(cx), float(cy), float(r), shape, float(w), float(h)))

        # Pre-scan small rectangular/square pads. This lets us identify the tiny
        # macro helper circles sitting at their corners and skip them later.
        for layer in layers:
            if self.realistic_layer_role(layer) != "copper":
                continue
            for prim in layer.primitives:
                if not allowed(layer, prim):
                    continue
                if prim.kind == "rect" and prim.points:
                    c = prim.points[0]
                    w, h = prim.rect or (0.2, 0.2)
                    if 0.05 <= min(abs(w), abs(h)) and max(abs(w), abs(h)) <= 8.0:
                        rr = QRectF(c.x() - w / 2, c.y() - h / 2, abs(w), abs(h)).normalized()
                        rect_candidates.append((rr.center().x(), rr.center().y(), rr.width(), rr.height(), rr))
                elif prim.kind == "polygon" and len(prim.points) >= 3:
                    poly = QPolygonF(prim.points)
                    rr = poly.boundingRect().normalized()
                    if 0.05 <= min(rr.width(), rr.height()) and max(rr.width(), rr.height()) <= 8.0:
                        aspect = rr.width() / max(rr.height(), 1e-9)
                        # Small macro square/rect pads. Do not treat long traces/pours as pads.
                        if 0.45 <= aspect <= 2.25:
                            rect_candidates.append((rr.center().x(), rr.center().y(), rr.width(), rr.height(), rr))

        def is_corner_helper_circle(cx: float, cy: float, r: float) -> bool:
            """True only for small macro circles located on a known rectangle corner."""
            for rcx, rcy, rw, rh, rr in rect_candidates:
                if r > min(rw, rh) * 0.30:
                    continue
                # Circle must be close to one of the four rectangle corners.
                corners = (
                    (rr.left(), rr.top()), (rr.right(), rr.top()),
                    (rr.right(), rr.bottom()), (rr.left(), rr.bottom()),
                )
                tol = max(0.035, r * 1.55)
                for kx, ky in corners:
                    if (cx - kx) * (cx - kx) + (cy - ky) * (cy - ky) <= tol * tol:
                        return True
            return False

        for layer in layers:
            if self.realistic_layer_role(layer) != "copper":
                continue
            for prim in layer.primitives:
                if not allowed(layer, prim):
                    continue

                if prim.kind == "circle" and prim.points:
                    center, r = prim.points[0], max(prim.radius, 0.001)
                    if r <= 2.8:
                        if is_corner_helper_circle(center.x(), center.y(), r):
                            continue
                        set_gold_for_circle(center, r)
                        p.drawEllipse(center, r, r)
                        remember_pad(center.x(), center.y(), r, "round", r * 2.0, r * 2.0)

                elif prim.kind == "rect" and prim.points:
                    c = prim.points[0]
                    w, h = prim.rect or (0.2, 0.2)
                    if max(abs(w), abs(h)) <= 6.0:
                        rr = QRectF(c.x() - w / 2, c.y() - h / 2, w, h).normalized()
                        set_gold_for_rect(rr)
                        p.drawRect(rr)
                        remember_pad(rr.center().x(), rr.center().y(), min(rr.width(), rr.height()) / 2.0, "rect", rr.width(), rr.height())

                elif prim.kind == "obround" and prim.points:
                    c = prim.points[0]
                    w, h = prim.rect or (0.2, 0.2)
                    if max(abs(w), abs(h)) <= 8.0:
                        rr = QRectF(c.x() - w / 2, c.y() - h / 2, w, h).normalized()
                        rad = min(rr.width(), rr.height()) / 2.0
                        set_gold_for_rect(rr)
                        p.drawRoundedRect(rr, rad, rad)
                        remember_pad(rr.center().x(), rr.center().y(), min(rr.width(), rr.height()) / 2.0, "obround", rr.width(), rr.height())

                elif prim.kind == "polygon" and len(prim.points) >= 3:
                    poly = QPolygonF(prim.points)
                    rr = poly.boundingRect().normalized()
                    if max(rr.width(), rr.height()) <= 8.0:
                        aspect = rr.width() / max(rr.height(), 1e-9)
                        # Small rectangular/square macro pads are exported as a polygon.
                        # In realistic mode draw them as a clean pad body, not as a
                        # rounded-corner helper construction.
                        if 0.45 <= aspect <= 2.25 and min(rr.width(), rr.height()) >= 0.05:
                            set_gold_for_rect(rr)
                            p.drawRect(rr)
                            remember_pad(rr.center().x(), rr.center().y(), min(rr.width(), rr.height()) / 2.0, "rect", rr.width(), rr.height())
                        else:
                            set_gold_for_rect(rr)
                            p.drawPolygon(poly)
                            remember_pad(rr.center().x(), rr.center().y(), min(rr.width(), rr.height()) / 2.0, "poly", rr.width(), rr.height())

        return pad_specs

    @staticmethod
    def _nearest_realistic_pad_radius(x: float, y: float, pad_specs: list) -> Optional[float]:
        """Return equivalent radius of the pad centered nearest to a drill hit."""
        best_r = None
        best_d2 = None
        for spec in pad_specs or []:
            px, py, pr = spec[0], spec[1], spec[2]
            # Through-hole drills and copper flashes should share almost the same centre.
            # Allow a tolerance that scales with pad size for slightly rounded exports.
            tol = max(0.08, pr * 0.45)
            dx = x - px
            dy = y - py
            d2 = dx * dx + dy * dy
            if d2 <= tol * tol and (best_d2 is None or d2 < best_d2):
                best_d2 = d2
                best_r = pr
        return best_r

    def draw_realistic_drill_holes(self, p: QPainter, layers: List[Layer], board_ref: QRectF, pad_specs: Optional[list] = None):
        """Paint drill holes as real openings, not as oversized black pads.

        Fix for plated through holes in realistic export:
        - black area is the hole only;
        - copper/gold annular ring remains visible;
        - malformed or old drill data is clamped against the nearest copper pad.
        """
        p.setPen(Qt.PenStyle.NoPen)
        pad_specs = pad_specs or []

        for layer in layers:
            if self.realistic_layer_role(layer) != "drill":
                continue
            for prim in layer.primitives:
                pb = self.primitive_bounds(prim)
                if (
                    not getattr(self, "_export_no_heuristic_filter", False)
                    and board_ref.isValid()
                    and not self.primitive_allowed_bounds(layer, pb, board_ref)
                ):
                    continue

                if prim.kind == "circle" and prim.points:
                    c = prim.points[0]
                    drill_r = max(float(prim.radius), 0.001)
                    pad_r = self._nearest_realistic_pad_radius(c.x(), c.y(), pad_specs)

                    # If a matching copper flash exists, use it as the outside of the
                    # plated annular ring.  If not, synthesize a realistic PTH ring
                    # around the drill.  This fixes connector/via holes that were
                    # rendered as black holes with green soldermask halo only.
                    if pad_r is not None:
                        outer_r = max(pad_r, drill_r * 1.55)
                        hole_r = min(drill_r, outer_r * 0.52)
                        hole_r = max(hole_r, min(outer_r * 0.28, drill_r))
                    else:
                        outer_r = max(drill_r * 1.72, drill_r + 0.18)
                        # Avoid absurd gold donuts from malformed large NPTH tools;
                        # mounting holes still keep a gold annular finish like the reference.
                        outer_r = min(outer_r, drill_r + 0.85)
                        hole_r = drill_r

                    # ENIG/gold annular ring, then dark barrel, then real opening.
                    rr = QRectF(c.x() - outer_r, c.y() - outer_r, 2.0 * outer_r, 2.0 * outer_r).normalized()
                    grad = QRadialGradient(c, max(outer_r, 0.001), QPointF(c.x() - outer_r * 0.30, c.y() + outer_r * 0.28))
                    grad.setColorAt(0.00, REALISTIC_GOLD_LIGHT)
                    grad.setColorAt(0.54, REALISTIC_GOLD_MID)
                    grad.setColorAt(1.00, REALISTIC_GOLD_DARK)
                    p.setBrush(QBrush(grad))
                    p.drawEllipse(c, outer_r, outer_r)

                    rim_r = hole_r * 1.10
                    p.setBrush(QBrush(QColor(18, 45, 10, 255)))
                    p.drawEllipse(c, rim_r, rim_r)
                    p.setBrush(QBrush(QColor(0, 0, 0, 255)))
                    p.drawEllipse(c, hole_r, hole_r)

                elif prim.kind == "line" and len(prim.points) >= 2:
                    # Slot drill: draw gold plated slot first, then the black routed
                    # opening.  This keeps slotted THT pads plated on both sides.
                    w = max(float(prim.width), 0.05)
                    p1, p2 = prim.points[0], prim.points[1]
                    pad_r1 = self._nearest_realistic_pad_radius(p1.x(), p1.y(), pad_specs)
                    pad_r2 = self._nearest_realistic_pad_radius(p2.x(), p2.y(), pad_specs)
                    pr = pad_r1 or pad_r2
                    outer_w = max(w * 1.70, w + 0.30) if pr is None else max(w * 1.25, pr * 1.55)
                    if pr is not None:
                        w = min(w, pr * 1.04)
                    p.setBrush(Qt.BrushStyle.NoBrush)
                    p.setPen(QPen(REALISTIC_GOLD_MID, outer_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                    p.drawLine(p1, p2)
                    p.setPen(QPen(QColor(0, 0, 0, 255), w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                    p.drawLine(p1, p2)
                    p.setPen(Qt.PenStyle.NoPen)


class ImageCanvas(QWidget):
    layerClicked = pyqtSignal(object)

    def __init__(self):
        super().__init__()
        self.pixmap: Optional[QPixmap] = None
        self.scale = 1.0
        self.center = QPointF(0, 0)
        self.last_mouse = QPointF()
        self.panning = False
        self.measure_mode = False
        self.measure_points: List[QPointF] = []

        self.bg = QColor(7, 11, 20)
        self.setMinimumSize(QSize(850, 650))
        self.setMouseTracking(True)

        self.world_bounds = QRectF()
        self.px_per_mm = 1.0
        self.margin_px = 80
        self.layers: List[Layer] = []
        self.active_pick_layers: List[Layer] = []   # selected layer rows in the table
        self.highlight: Optional[Tuple[Layer, Optional[Primitive]]] = None
        self.hover_world: Optional[QPointF] = None

        self._highlight_cache_key = None
        self._highlight_cache_pixmap: Optional[QPixmap] = None

        self.vector_mode = True
        self._vector_helper = RasterRenderer()

        self.nav_active = False
        self.nav_cache: Optional[QPixmap] = None
        self.nav_start_center = QPointF(0, 0)
        self.nav_start_scale = 1.0
        self.nav_timer = QTimer(self)
        self.nav_timer.setSingleShot(True)
        self.nav_timer.timeout.connect(self.finish_smooth_navigation)
        self.repaint_clock = QElapsedTimer()
        self.repaint_clock.start()
        self.hover_clock = QElapsedTimer()
        self.hover_clock.start()

        self.pan_update_interval_ms = 5
        self.hover_update_interval_ms = 120
        self.zoom_finish_delay_ms = 85
        self.zoom_update_interval_ms = 5
        self.zooming = False
        self.low_quality_navigation = False
        self.vector_lod_px = 1.35
        self._cached_board_ref = QRectF()
        self._cached_ordered_layers: List[Layer] = []
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, True)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self.setAttribute(Qt.WidgetAttribute.WA_StaticContents, True)

    def set_image(self, image: QImage, preserve_view: bool = False):
        old_center = QPointF(self.center)
        old_scale = float(self.scale)
        had_pixmap = self.pixmap is not None

        self.pixmap = QPixmap.fromImage(image)

        if preserve_view and had_pixmap:
            self.center = old_center
            self.scale = old_scale
            self.update()
            return

        self.center = QPointF(self.pixmap.width() / 2, self.pixmap.height() / 2)
        QTimer.singleShot(0, self.fit)
        QTimer.singleShot(80, self.fit)
        self.update()

    def set_scene(self, layers: List[Layer], world_bounds: QRectF, px_per_mm: float, margin_px: int):
        self.layers = layers
        self.world_bounds = QRectF(world_bounds)
        self.px_per_mm = max(float(px_per_mm), 1e-9)
        self.margin_px = int(margin_px)

        self.nav_active = False
        self.low_quality_navigation = False
        self.nav_cache = None

        for layer in self.layers:
            setattr(layer, "_viewport_candidate_cache", None)

        self.invalidate_highlight_cache()
        self.rebuild_navigation_caches()
        self.update()

    @staticmethod
    def layer_order_key(layer: Layer) -> int:
        n = layer.name.lower()
        if "copper" in n or "signal" in n:
            return 10
        if "pads" in n:
            return 20
        if "mask" in n:
            return 30
        if "paste" in n:
            return 40
        if "profile" in n or "mechanical" in n:
            return 50
        if "legend" in n or "silk" in n:
            return 70
        if "drill" in n:
            return 80
        if "assembly" in n:
            return 90
        return 60

    def rebuild_navigation_caches(self):
        try:
            self._cached_board_ref = self._vector_helper.main_board_reference(self.layers)
            self._cached_ordered_layers = sorted(self.layers, key=self.layer_order_key)
        except Exception:
            self._cached_board_ref = QRectF()
            self._cached_ordered_layers = list(self.layers)

    def begin_smooth_navigation(self):
        """Live-vector navigation with one true coordinate system.

        The previous framebuffer snapshot cache was fast but could visually
        drift and snap back on mouse release because the temporary pixmap and
        final vector scene used different transforms.  This version keeps only
        center/scale as the single source of truth.
        """
        self.nav_active = False
        self.nav_cache = None
        self.low_quality_navigation = True

    def finish_smooth_navigation(self):
        self.nav_active = False
        self.nav_cache = None
        self.zooming = False
        self.low_quality_navigation = False
        self.update()

    def draw_smooth_navigation_cache(self, p: QPainter) -> bool:
        return False

    def invalidate_highlight_cache(self):
        self._highlight_cache_key = None
        self._highlight_cache_pixmap = None

    def set_active_pick_layers(self, layers: List[Layer]):
        self.active_pick_layers = [l for l in layers if l and l.visible]
        if self.highlight and self.active_pick_layers and self.highlight[0] not in self.active_pick_layers:
            self.highlight = None
        self.invalidate_highlight_cache()
        self.update()

    def image_to_world(self, ip: QPointF) -> QPointF:
        if not self.world_bounds.isValid():
            return QPointF()
        x = self.world_bounds.left() + (ip.x() - self.margin_px) / self.px_per_mm
        y = self.world_bounds.bottom() - (ip.y() - self.margin_px) / self.px_per_mm
        return QPointF(x, y)

    def world_to_image(self, wp: QPointF) -> QPointF:
        if not self.world_bounds.isValid():
            return QPointF()
        x = self.margin_px + (wp.x() - self.world_bounds.left()) * self.px_per_mm
        y = self.margin_px + (self.world_bounds.bottom() - wp.y()) * self.px_per_mm
        return QPointF(x, y)

    def screen_to_world(self, sp: QPointF) -> QPointF:
        return self.image_to_world(self.screen_to_image(sp))

    def world_to_screen(self, wp: QPointF) -> QPointF:
        return self.image_to_screen(self.world_to_image(wp))

    def fit(self):
        if not self.pixmap:
            return
        margin = 35
        avail_w = max(50, self.width() - 2 * margin)
        avail_h = max(50, self.height() - 2 * margin)
        self.scale = min(
            avail_w / max(self.pixmap.width(), 1),
            avail_h / max(self.pixmap.height(), 1),
        )
        self.scale = max(0.01, self.scale)
        self.center = QPointF(self.pixmap.width() / 2, self.pixmap.height() / 2)
        self.update()

    def center_image(self):
        if not self.pixmap:
            return
        self.center = QPointF(self.pixmap.width() / 2, self.pixmap.height() / 2)
        self.update()

    def image_rect_screen(self) -> QRectF:
        if not self.pixmap:
            return QRectF()
        x = self.width()/2 - self.center.x() * self.scale
        y = self.height()/2 - self.center.y() * self.scale
        return QRectF(x, y, self.pixmap.width()*self.scale, self.pixmap.height()*self.scale)

    def screen_to_image(self, pt: QPointF) -> QPointF:
        return QPointF(
            self.center.x() + (pt.x() - self.width()/2) / max(self.scale, 1e-9),
            self.center.y() + (pt.y() - self.height()/2) / max(self.scale, 1e-9),
        )

    def image_to_screen(self, pt: QPointF) -> QPointF:
        return QPointF(
            self.width()/2 + (pt.x() - self.center.x()) * self.scale,
            self.height()/2 + (pt.y() - self.center.y()) * self.scale,
        )

    def draw_vector_scene(self, p: QPainter):
        """Draw Gerber primitives directly in vector mode.

        Final repaint is always true vector, so zoom remains sharp. During
        active navigation, paintEvent uses the fast cache instead.
        """
        if not self.layers or not self.world_bounds.isValid():
            return False

        p.save()
        moving = bool(getattr(self, "low_quality_navigation", False))
        highlighted = self.highlight is not None
        p.setRenderHint(QPainter.RenderHint.Antialiasing, not moving)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing, not moving)

        p.translate(self.width()/2 - self.center.x() * self.scale,
                    self.height()/2 - self.center.y() * self.scale)
        p.scale(self.scale, self.scale)

        wb = self.world_bounds.normalized()
        p.translate(self.margin_px - wb.left() * self.px_per_mm,
                    self.margin_px + wb.bottom() * self.px_per_mm)
        p.scale(self.px_per_mm, -self.px_per_mm)

        w0 = self.screen_to_world(QPointF(0, 0))
        w1 = self.screen_to_world(QPointF(self.width(), self.height()))
        view_world = QRectF(w0, w1).normalized()
        pad = max(2.0, 28.0 / max(self.scale * self.px_per_mm, 1e-9))
        self._vector_helper.current_view_world = view_world.adjusted(-pad, -pad, pad, pad)
        self._vector_helper.current_screen_px_per_mm = self.scale * self.px_per_mm
        self._vector_helper.current_lod_px = 0.0

        visible_layers = [l for l in self.layers if l.visible]
        if len(visible_layers) == 1:
            board_ref = QRectF()
        else:
            board_ref = self._cached_board_ref if self._cached_board_ref.isValid() else self._vector_helper.main_board_reference(self.layers)
        ordered_layers = self._cached_ordered_layers if self._cached_ordered_layers else sorted(self.layers, key=self.layer_order_key)

        for layer in ordered_layers:
            if not layer.visible:
                continue


            self._vector_helper.draw_layer(p, layer, board_ref)

        for _attr in ("current_view_world", "current_screen_px_per_mm", "current_lod_px"):
            if hasattr(self._vector_helper, _attr):
                delattr(self._vector_helper, _attr)

        p.restore()
        return True

    def paintEvent(self, event):
        p = QPainter(self)
        p.fillRect(self.rect(), self.bg)

        if False and self.draw_smooth_navigation_cache(p):
            p.setPen(QColor(235, 235, 235))
            p.setFont(QFont("Segoe UI", 9))
            p.drawText(12, self.height() - 14,
                       f"ULTRA GERBER VIEWER by George Kourtidis | LIVE INSTANT VECTOR | scale={self.scale:.4f}")
            return

        drew_vector = False

        nav_preview = bool(self.low_quality_navigation and self.pixmap is not None)

        if nav_preview:
            p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
            p.setRenderHint(QPainter.RenderHint.TextAntialiasing, False)
            p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, False)
            p.drawPixmap(self.image_rect_screen(), self.pixmap, QRectF(0, 0, self.pixmap.width(), self.pixmap.height()))
        else:
            if self.vector_mode:
                drew_vector = self.draw_vector_scene(p)

            if not drew_vector:
                if self.pixmap:
                    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, self.scale < 2.0)
                    p.drawPixmap(self.image_rect_screen(), self.pixmap, QRectF(0, 0, self.pixmap.width(), self.pixmap.height()))
                else:
                    p.setPen(QColor(220, 220, 220))
                    p.setFont(QFont("Segoe UI", 13))
                    p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "Open Gerber / Drill files")

        self.draw_highlight(p)
        self.draw_measure(p)

        p.setPen(QColor(235, 235, 235))
        p.setFont(QFont("Segoe UI", 9))
        mode = "MEASURE" if self.measure_mode else "PAN"
        extra = " | FAST PREVIEW" if self.low_quality_navigation and self.pixmap is not None else (" | LIVE VECTOR" if drew_vector else " | RASTER")
        if self.hover_world is not None:
            extra += f" | X={self.hover_world.x():.3f} mm Y={self.hover_world.y():.3f} mm"
        if self.active_pick_layers:
            extra += " | PICK LAYER: " + ",".join(l.name for l in self.active_pick_layers[:2])
            if len(self.active_pick_layers) > 2:
                extra += f"+{len(self.active_pick_layers)-2}"
        else:
            extra += " | PICK LAYER: top visible"
        if self.highlight and getattr(self, "low_quality_navigation", False):
            pass
        elif self.highlight:
            extra += f" | HIGHLIGHT LAYER: {self.highlight[0].name}"
        p.drawText(12, self.height() - 14, f"ULTRA GERBER VIEWER by George Kourtidis | {mode} | scale={self.scale:.4f}{extra}")

    def draw_measure(self, p: QPainter):
        if not self.pixmap:
            return

        pts = list(self.measure_points)
        if self.measure_mode and len(pts) == 1:
            pts.append(self.screen_to_image(self.mapFromGlobal(self.cursor().pos())))

        if not pts:
            return

        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.setPen(QPen(QColor(255, 230, 120), 2))
        p.setBrush(QBrush(QColor(255, 230, 120)))

        for ip in pts[:2]:
            sp = self.image_to_screen(ip)
            p.drawEllipse(sp, 4, 4)

        if len(pts) >= 2:
            a, b = pts[0], pts[1]
            sa, sb = self.image_to_screen(a), self.image_to_screen(b)
            p.drawLine(sa, sb)

            aw = self.image_to_world(a)
            bw = self.image_to_world(b)
            dx = bw.x() - aw.x()
            dy = bw.y() - aw.y()
            d = math.hypot(dx, dy)
            label = f"{d:.3f} mm   dx={dx:.3f}   dy={dy:.3f}"

            mid = QPointF((sa.x()+sb.x())/2, (sa.y()+sb.y())/2)
            p.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
            fm = p.fontMetrics()
            rr = QRectF(mid.x()+10, mid.y()-25, fm.horizontalAdvance(label)+14, 24)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(0, 0, 0, 190))
            p.drawRoundedRect(rr, 5, 5)
            p.setPen(QColor(255, 230, 120))
            p.drawText(rr.adjusted(7, 0, 0, 0), Qt.AlignmentFlag.AlignVCenter, label)

    def draw_highlight(self, p: QPainter):
        if not self.pixmap or not self.highlight:
            return

        layer, picked_prim = self.highlight
        if not layer.visible:
            return

        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        base = layer.color
        glow = QColor(base.red(), base.green(), base.blue(), 255)
        fill = QColor(base.red(), base.green(), base.blue(), 120)

        def draw_prim(prim: Primitive, strong: bool = False):
            extra = 3 if strong else 0

            def path_from_points(points: List[QPointF]) -> QPainterPath:
                path = QPainterPath()
                if not points:
                    return path
                path.moveTo(self.world_to_screen(points[0]))
                for pt in points[1:]:
                    path.lineTo(self.world_to_screen(pt))
                return path

            if prim.kind == "line" and len(prim.points) >= 2:
                pen_w = max(4.0, (prim.width * self.px_per_mm * self.scale) + 4.0 + extra)
                p.setPen(QPen(glow, pen_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawLine(self.world_to_screen(prim.points[0]), self.world_to_screen(prim.points[1]))

            elif prim.kind == "polyline" and len(prim.points) >= 2:
                pen_w = max(4.0, (prim.width * self.px_per_mm * self.scale) + 4.0 + extra)
                p.setPen(QPen(glow, pen_w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawPath(path_from_points(prim.points))

            elif prim.kind == "region" and prim.contours:
                path = QPainterPath()
                path.setFillRule(Qt.FillRule.OddEvenFill)
                for contour in prim.contours:
                    if len(contour) < 3:
                        continue
                    path.moveTo(self.world_to_screen(contour[0]))
                    for pt in contour[1:]:
                        path.lineTo(self.world_to_screen(pt))
                    path.closeSubpath()
                p.setPen(QPen(glow, 2 + extra))
                p.setBrush(QBrush(fill))
                p.drawPath(path)

            elif prim.kind == "circle" and prim.points:
                c = self.world_to_screen(prim.points[0])
                r = max(2.0, prim.radius * self.px_per_mm * self.scale)
                p.setPen(QPen(glow, 3 + extra))
                p.setBrush(QBrush(fill))
                p.drawEllipse(c, r + 2 + extra, r + 2 + extra)

            elif prim.kind in ("rect", "obround") and prim.points:
                c = prim.points[0]
                w, h = prim.rect or (0.2, 0.2)
                a = self.world_to_screen(QPointF(c.x() - w/2, c.y() + h/2))
                b = self.world_to_screen(QPointF(c.x() + w/2, c.y() - h/2))
                rr = QRectF(a, b).normalized().adjusted(-2-extra, -2-extra, 2+extra, 2+extra)
                p.setPen(QPen(glow, 3 + extra))
                p.setBrush(QBrush(fill))
                if prim.kind == "obround":
                    p.drawRoundedRect(rr, min(rr.width(), rr.height()) / 2, min(rr.width(), rr.height()) / 2)
                else:
                    p.drawRect(rr)

            elif prim.kind == "polygon" and len(prim.points) >= 3:
                poly = QPolygonF([self.world_to_screen(pt) for pt in prim.points])
                p.setPen(QPen(glow, 3 + extra))
                p.setBrush(QBrush(fill))
                p.drawPolygon(poly, Qt.FillRule.OddEvenFill)

        for prim in layer.primitives:
            draw_prim(prim, strong=(prim is picked_prim))

    @staticmethod
    def _dist_point_segment(p: QPointF, a: QPointF, b: QPointF) -> float:
        ax, ay, bx, by = a.x(), a.y(), b.x(), b.y()
        px, py = p.x(), p.y()
        vx, vy = bx - ax, by - ay
        wx, wy = px - ax, py - ay
        vv = vx * vx + vy * vy
        if vv <= 1e-18:
            return math.hypot(px - ax, py - ay)
        t = max(0.0, min(1.0, (wx * vx + wy * vy) / vv))
        qx, qy = ax + t * vx, ay + t * vy
        return math.hypot(px - qx, py - qy)

    @staticmethod
    def _point_in_poly(p: QPointF, pts: List[QPointF]) -> bool:
        inside = False
        n = len(pts)
        if n < 3:
            return False
        x, y = p.x(), p.y()
        j = n - 1
        for i in range(n):
            xi, yi = pts[i].x(), pts[i].y()
            xj, yj = pts[j].x(), pts[j].y()
            if ((yi > y) != (yj > y)) and (x < (xj - xi) * (y - yi) / ((yj - yi) or 1e-18) + xi):
                inside = not inside
            j = i
        return inside

    def primitive_distance_mm(self, wp: QPointF, prim: Primitive) -> float:
        inf = 1e18

        if prim.kind == "line" and len(prim.points) >= 2:
            return max(0.0, self._dist_point_segment(wp, prim.points[0], prim.points[1]) - prim.width / 2)

        if prim.kind == "polyline" and len(prim.points) >= 2:
            d = min(self._dist_point_segment(wp, prim.points[i], prim.points[i + 1]) for i in range(len(prim.points) - 1))
            return max(0.0, d - prim.width / 2)

        if prim.kind == "circle" and prim.points:
            return abs(math.hypot(wp.x() - prim.points[0].x(), wp.y() - prim.points[0].y()) - prim.radius)

        if prim.kind in ("rect", "obround") and prim.points:
            c = prim.points[0]
            w, h = prim.rect or (0.2, 0.2)
            dx = max(abs(wp.x() - c.x()) - w / 2, 0.0)
            dy = max(abs(wp.y() - c.y()) - h / 2, 0.0)
            return math.hypot(dx, dy)

        if prim.kind == "polygon" and len(prim.points) >= 3:
            if self._point_in_poly(wp, prim.points):
                return 0.0
            return min(self._dist_point_segment(wp, prim.points[i], prim.points[(i + 1) % len(prim.points)]) for i in range(len(prim.points)))

        if prim.kind == "region" and prim.contours:
            best = inf
            for contour in prim.contours:
                if len(contour) < 3:
                    continue
                if self._point_in_poly(wp, contour):
                    return 0.0
                best = min(best, min(self._dist_point_segment(wp, contour[i], contour[(i + 1) % len(contour)]) for i in range(len(contour))))
            return best

        return inf

    def hit_test(self, sp: QPointF, ignore_active_pick_layers: bool = False) -> Optional[Tuple[Layer, Primitive, float]]:
        wp = self.screen_to_world(sp)
        tol_mm = max(0.12, 9.0 / (self.scale * self.px_per_mm))
        best: Optional[Tuple[Layer, Primitive, float]] = None

        pick_layers = ([l for l in reversed(self.layers) if l.visible] if ignore_active_pick_layers else (self.active_pick_layers if self.active_pick_layers else [l for l in reversed(self.layers) if l.visible]))

        for layer in pick_layers:
            if not layer.visible:
                continue
            for prim in reversed(layer.primitives):
                d = self.primitive_distance_mm(wp, prim)
                if d <= tol_mm and (best is None or d < best[2]):
                    best = (layer, prim, d)

        return best

    def wheelEvent(self, e: QWheelEvent):
        if not self.pixmap:
            return

        mouse_pos = e.position()
        before = self.screen_to_image(mouse_pos)

        steps = e.angleDelta().y() / 120.0
        factor = 1.18 ** steps
        old_scale = float(self.scale)
        self.scale = max(0.005, min(350.0, old_scale * factor))

        self.center = QPointF(
            before.x() - (mouse_pos.x() - self.width() / 2.0) / max(self.scale, 1e-9),
            before.y() - (mouse_pos.y() - self.height() / 2.0) / max(self.scale, 1e-9)
        )

        self.nav_active = False
        self.nav_cache = None
        self.zooming = True
        self.low_quality_navigation = True
        self.nav_timer.start(self.zoom_finish_delay_ms)
        self.update()

    def mouseDoubleClickEvent(self, e: QMouseEvent):
        if e.button() == Qt.MouseButton.LeftButton:
            hit = self.hit_test(e.position(), ignore_active_pick_layers=True)
            if hit:
                self.highlight = (hit[0], hit[1])
                self.layerClicked.emit(hit[0])
            else:
                self.highlight = None
            self.update()
            e.accept()
            return

        super().mouseDoubleClickEvent(e)

    def mousePressEvent(self, e: QMouseEvent):
        if self.measure_mode and e.button() == Qt.MouseButton.LeftButton:
            ip = self.screen_to_image(e.position())
            if len(self.measure_points) >= 2:
                self.measure_points.clear()
            self.measure_points.append(ip)
            self.update()
            return

        if e.button() == Qt.MouseButton.LeftButton:
            hit = self.hit_test(e.position())
            if hit:
                if self.highlight and self.highlight[0] is hit[0]:
                    self.highlight = None
                else:
                    self.highlight = (hit[0], hit[1])
                self.layerClicked.emit(hit[0])
            else:
                self.highlight = None
            self.update()
            return

        if e.button() in (Qt.MouseButton.MiddleButton, Qt.MouseButton.RightButton):
            self.nav_timer.stop()
            self.zooming = False
            self.nav_active = False
            self.nav_cache = None
            self.low_quality_navigation = True
            self.panning = True
            self.last_mouse = e.position()
            self.setCursor(Qt.CursorShape.ClosedHandCursor)

    def mouseMoveEvent(self, e: QMouseEvent):
        if self.pixmap:
            self.hover_world = self.screen_to_world(e.position())

        if self.panning and self.pixmap:
            self.nav_active = False
            self.nav_cache = None
            self.low_quality_navigation = True
            delta = e.position() - self.last_mouse
            self.center -= QPointF(
                delta.x() / max(self.scale, 1e-9),
                delta.y() / max(self.scale, 1e-9)
            )
            self.last_mouse = e.position()

            if self.repaint_clock.elapsed() >= self.pan_update_interval_ms:
                self.repaint_clock.restart()
                self.update()
            return

        if self.measure_mode or self.hover_clock.elapsed() >= self.hover_update_interval_ms:
            self.hover_clock.restart()
            self.update()

    def mouseReleaseEvent(self, e: QMouseEvent):
        self.panning = False
        self.setCursor(Qt.CursorShape.ArrowCursor)

        self.nav_timer.stop()
        self.nav_active = False
        self.nav_cache = None
        self.zooming = False
        self.low_quality_navigation = False
        self.update()

    def toggle_measure(self):
        self.measure_mode = not self.measure_mode
        self.measure_points.clear()
        self.update()

    def clear_measure(self):
        self.measure_points.clear()
        self.update()

    def clear_highlight(self):
        self.highlight = None
        self.invalidate_highlight_cache()
        self.update()


class LayerColorDelegate(QStyledItemDelegate):
    """Paint the Color column manually so row selection never hides the layer color square."""

    def paint(self, painter: QPainter, option, index):
        painter.save()

        layer = index.data(Qt.ItemDataRole.UserRole)
        if layer is not None and hasattr(layer, "color"):
            color = QColor(layer.color)
            color.setAlpha(255)
        else:
            color = QColor(92, 225, 255)

        selected = bool(option.state & QStyle.StateFlag.State_Selected) if "QStyle" in globals() else False

        if selected:
            painter.fillRect(option.rect, QColor(0, 208, 255))
        else:
            painter.fillRect(option.rect, QColor(11, 23, 40))

        size = max(10, min(15, option.rect.height() - 12))
        x = option.rect.left() + 10
        y = option.rect.top() + (option.rect.height() - size) // 2
        square = QRectF(x, y, size, size)

        painter.setPen(QPen(QColor(0, 18, 28), 1))
        painter.setBrush(QBrush(color))
        painter.drawRect(square)

        painter.restore()


class MainWindow(QMainWindow):
    COLORS = [
        QColor(0, 255, 194, 235),    # Ultra cyan / copper-pop
        QColor(255, 74, 128, 235),   # Hot magenta-red
        QColor(255, 208, 66, 235),   # Premium gold
        QColor(92, 225, 255, 235),   # Electric blue
        QColor(150, 108, 255, 235),  # Violet
        QColor(68, 255, 119, 235),   # Signal green
        QColor(255, 143, 51, 235),   # Amber orange
        QColor(235, 242, 255, 235),  # Ice white
    ]

    def __init__(self):
        super().__init__()
        self.setWindowTitle("ULTRA GERBER VIEWER by George Kourtidis")
        self.resize(1550, 920)

        self.layers: List[Layer] = []
        self.renderer = RasterRenderer()
        self.canvas = ImageCanvas()

        self.table = QTableWidget(0, 4)
        self.log = QTextEdit(readOnly=True)
        self.status = QLabel("Ready")
        self._block_table = False

        side = QFrame()
        side.setMinimumWidth(430)
        side.setMaximumWidth(570)
        side.setStyleSheet("""
            QFrame {
                background:#07111f;
                color:#eaf2ff;
                font-family:'Segoe UI';
            }
            QPushButton {
                padding:8px;
                background:#10233a;
                color:#f4f8ff;
                border:1px solid #1f9eff;
                border-radius:8px;
                font-weight:600;
            }
            QPushButton:hover {
                background:#16395f;
                border:1px solid #00ffc2;
            }
            QPushButton:pressed {
                background:#00ffc2;
                color:#06101d;
            }
            QTableWidget, QTextEdit {
                background:#0b1728;
                border:1px solid #24527a;
                color:#f2f7ff;
                gridline-color:#20364d;
                selection-background-color:#00d0ff;
                selection-color:#001018;
            }
            QTableWidget::item:selected {
                background:#00d0ff;
                color:#001018;
                border:1px solid #5fe7ff;
                font-weight:700;
            }
            QTableWidget::item:hover {
                background:#103450;
            }
            QHeaderView::section {
                background:#10233a;
                color:#00ffc2;
                border:1px solid #24527a;
                padding:5px;
                font-weight:bold;
            }
            QLabel { color:#cfe7ff; }
            QTextEdit { color:#b9ffd8; }
        """)

        self.table.setHorizontalHeaderLabels(["ON", "Color", "Layer", "Info"])
        self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        self.table.horizontalHeader().setSectionResizeMode(2, QHeaderView.ResizeMode.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(3, QHeaderView.ResizeMode.Stretch)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.table.setAlternatingRowColors(False)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setItemDelegateForColumn(1, LayerColorDelegate(self.table))
        self.table.itemChanged.connect(self.table_changed)
        self.table.itemSelectionChanged.connect(self.update_pick_layers)
        self.table.itemDoubleClicked.connect(self.highlight_from_table)
        self.canvas.layerClicked.connect(self.select_layer_row)

        buttons = [
            ("Open Gerber / Drill", self.open_files),
            ("Open Folder", self.open_folder),
            ("Render", self.render_visible),
            ("Top View", self.top_view),
            ("Bottom View", self.bottom_view),
            ("Production View", self.clean_view),
            ("Top Copper Only", self.top_copper_only),
            ("Bottom Copper Only", self.bottom_copper_only),
            ("Both Copper", self.both_copper_view),
            ("Silks Only", self.silk_only_view),
            ("Mask Only", self.mask_only_view),
            ("Paste Only", self.paste_only_view),
            ("Drill / Outline", self.drill_outline_view),
            ("Solo Selected", self.solo_selected_layer),
            ("Restore All", lambda: self.set_all(True)),
            ("FIT", self.canvas.fit),
            ("CENTER", self.canvas.center_image),
            ("Measure", self.canvas.toggle_measure),
            ("Clear Measure", self.canvas.clear_measure),
            ("Highlight Layer", self.highlight_from_table),
            ("Clear Highlight", self.canvas.clear_highlight),
            ("Change Color", self.change_color),
            ("Use All Colors", self.use_all_layer_colors),
            ("All ON", lambda: self.set_all(True)),
            ("All OFF", lambda: self.set_all(False)),
            ("Clear", self.clear_all),
        ]

        layout = QVBoxLayout(side)
        title = QLabel("ULTRA GERBER VIEWER\nby George Kourtidis")
        title.setStyleSheet("""
            font-size:21px;
            font-weight:900;
            color:#00ffc2;
            padding:10px;
            border:1px solid #1f9eff;
            border-radius:10px;
            background:#0b1728;
            letter-spacing:1px;
        """)
        layout.addWidget(title)

        for i in range(0, len(buttons), 2):
            h = QHBoxLayout()
            for text, fn in buttons[i:i+2]:
                b = QPushButton(text)
                b.clicked.connect(fn)
                h.addWidget(b)
            layout.addLayout(h)

        layout.addWidget(QLabel("Layers"))
        layout.addWidget(self.table, 3)
        layout.addWidget(QLabel("Log"))
        layout.addWidget(self.log, 1)
        layout.addWidget(self.status)

        sp = QSplitter()
        sp.addWidget(side)
        sp.addWidget(self.canvas)
        sp.setStretchFactor(1, 1)
        self.setCentralWidget(sp)
        self.menu()

    def menu(self):
        file_m = self.menuBar().addMenu("File")
        a = QAction("Open", self)
        a.setShortcut(QKeySequence.StandardKey.Open)
        a.triggered.connect(self.open_files)
        file_m.addAction(a)

        export_m = self.menuBar().addMenu("Export")

        exp_png = QAction("Export PNG Auto Side", self)
        exp_png.setShortcut("Ctrl+E")
        exp_png.triggered.connect(self.export_png)
        export_m.addAction(exp_png)

        exp_png_top = QAction("Export PNG Top Side", self)
        exp_png_top.triggered.connect(lambda: self.export_png(side="top"))
        export_m.addAction(exp_png_top)

        exp_png_bottom = QAction("Export PNG Bottom Side", self)
        exp_png_bottom.triggered.connect(lambda: self.export_png(side="bottom"))
        export_m.addAction(exp_png_bottom)

        export_m.addSeparator()

        exp_pdf = QAction("Export PDF", self)
        exp_pdf.setShortcut("Ctrl+Shift+E")
        exp_pdf.triggered.connect(self.export_pdf)
        export_m.addAction(exp_pdf)

        view_m = self.menuBar().addMenu("View")
        top = QAction("Top View", self)
        top.triggered.connect(self.top_view)
        view_m.addAction(top)
        bot = QAction("Bottom View", self)
        bot.triggered.connect(self.bottom_view)
        view_m.addAction(bot)
        prod = QAction("Production View", self)
        prod.triggered.connect(self.clean_view)
        view_m.addAction(prod)
        tco = QAction("Top Copper Only", self)
        tco.triggered.connect(self.top_copper_only)
        view_m.addAction(tco)
        bco = QAction("Bottom Copper Only", self)
        bco.triggered.connect(self.bottom_copper_only)
        view_m.addAction(bco)
        both = QAction("Both Copper", self)
        both.triggered.connect(self.both_copper_view)
        view_m.addAction(both)
        silk = QAction("Silks Only", self)
        silk.triggered.connect(self.silk_only_view)
        view_m.addAction(silk)
        mask = QAction("Mask Only", self)
        mask.triggered.connect(self.mask_only_view)
        view_m.addAction(mask)
        paste = QAction("Paste Only", self)
        paste.triggered.connect(self.paste_only_view)
        view_m.addAction(paste)
        drill = QAction("Drill / Outline", self)
        drill.triggered.connect(self.drill_outline_view)
        view_m.addAction(drill)
        f = QAction("FIT", self)
        f.setShortcut("F")
        f.triggered.connect(self.canvas.fit)
        view_m.addAction(f)

    def log_msg(self, s: str):
        self.log.append(s)
        self.status.setText(s)
        QApplication.processEvents()


    @staticmethod
    def read_gerber_attributes(path: str) -> Dict[str, str]:
        """Read X2 TF attributes from a Gerber header.

        This is intentionally lightweight and safe: it only reads the first part
        of the file and does not affect primitive parsing/rendering.  The result
        is used only by the layer buttons/presets.
        """
        out: Dict[str, str] = {}
        try:
            head = Path(path).read_text(errors="ignore")[:20000]
        except Exception:
            return out
        for m in re.finditer(r"%TF\.([^,\*%]+),([^\*%]+)\*%", head, re.I):
            out[m.group(1).strip().lower()] = m.group(2).strip().lower()
        return out

    @staticmethod
    def read_gerber_file_function(path: str) -> str:
        """Read X2 %TF.FileFunction,...*% from Gerber header, if present."""
        return MainWindow.read_gerber_attributes(path).get("filefunction", "")

    @staticmethod
    def normalized_cam_name(path: str) -> str:
        raw = Path(path).name.lower()
        return re.sub(r"[^a-z0-9]+", "_", raw).strip("_")

    @staticmethod
    def read_altium_extrep_description(path: str) -> str:
        """Return Altium/CAMtastic layer description from a sibling .EXTREP file.

        Old Altium/CAMtastic exports can use ambiguous extensions:
        .GP1/.GP2 = Internal Plane, .GPT/.GPB = Pad Master, .GTP/.GBP = Paste,
        .GM1/.GM2 = mechanical/documentation.  The .EXTREP file is the safest
        source and it lets this viewer load those jobs without hard-coding only
        one vendor's convention.
        """
        pp = Path(path)
        ext = pp.suffix.upper()
        candidates = [pp.with_suffix('.EXTREP'), pp.with_suffix('.extrep')]
        try:
            candidates.extend(pp.parent.glob('*.EXTREP'))
            candidates.extend(pp.parent.glob('*.extrep'))
        except Exception:
            pass

        seen = set()
        for c in candidates:
            try:
                c = Path(c)
                key = str(c).lower()
                if key in seen or not c.exists():
                    continue
                seen.add(key)
                text = c.read_text(errors='ignore')
                for line in text.splitlines():
                    m = re.match(r"\s*(\.[A-Za-z0-9]+)\s+(.+?)\s*$", line)
                    if m and m.group(1).upper() == ext:
                        desc = m.group(2).strip()
                        if desc and not set(desc) <= {'-'}:
                            return desc
            except Exception:
                continue
        return ""

    @staticmethod
    def detect_cad_family(path: str) -> str:
        """Best-effort CAM origin detector for UI grouping only.

        Handles naming families used by KiCad, Altium/Protel/CAMtastic, Eagle,
        Proteus/ARES, EasyEDA, DipTrace, PADS, OrCAD/Allegro, DesignSpark,
        Sprint-Layout/Target/Ultiboard and generic fab-house zips.
        """
        name = MainWindow.normalized_cam_name(path)
        attrs = MainWindow.read_gerber_attributes(path)
        gen = attrs.get("generationsoftware", "")
        ext = Path(path).suffix.lower()

        if "kicad" in gen or any(k in name for k in ("f_cu", "b_cu", "edge_cuts", "f_mask", "b_mask", "f_paste", "b_paste")):
            return "kicad"
        if "easyeda" in gen or name.startswith("gerber_") or any(k in name for k in ("topsoldermasklayer", "bottomsoldermasklayer", "topsilklayer", "bottomsilklayer", "boardoutlinelayer")):
            return "easyeda"
        if "altium" in gen or "protel" in gen or "camtastic" in gen or any(k in name for k in (
            "toplayer", "bottomlayer", "top_overlay", "bottom_overlay", "topoverlay", "bottomoverlay",
            "top_paste", "bottom_paste", "toppaste", "bottompaste", "top_solder", "bottom_solder",
            "drilldrawing", "drill_drawing", "keepout", "mechanical", "midlayer", "internalplane"
        )):
            return "altium/protel"
        if "eagle" in gen or ext in {".cmp", ".sol", ".plc", ".pls", ".stc", ".sts", ".crc", ".crs"} or any(k in name for k in ("dimension", "tcream", "bcream", "tsilk", "bsilk", "tstop", "bstop", "tplace", "bplace")):
            return "eagle"
        if "proteus" in gen or "ares" in gen or any(k in name for k in (
            "top_copper", "bottom_copper", "top_silk", "bottom_silk", "top_resist", "bottom_resist",
            "top_paste", "bottom_paste", "cadcam", "proteus", "ares"
        )):
            return "proteus/ares"
        if "diptrace" in gen or any(k in name for k in ("topmask", "bottommask", "topsilk", "bottomsilk", "boardoutline")):
            return "diptrace"
        if "pads" in gen or any(k in name for k in ("pads", "powerpcb", "smt", "smb", "sst", "ssb", "spt", "spb")):
            return "pads"
        if any(k in gen for k in ("orcad", "allegro", "cadence")) or ext == ".art":
            return "orcad/allegro"
        if any(k in gen for k in ("designspark", "ultiboard", "target", "sprint")):
            return "other-cad"
        if attrs.get("filefunction", ""):
            return "x2-gerber"
        return "generic"

    def classify_layer_type(self, path: str) -> str:
        """Classify a CAM file by real fabrication role.

        Priority is: metadata/X2 -> sidecar reports -> exact extension -> filename tokens.
        This prevents the TOP buttons from selecting top mask/silk when the requested
        role is top copper, and handles Proteus/ARES and other older CAD exports.
        """
        n = self.normalized_cam_name(path)
        raw = Path(path).name.lower()
        ext = Path(path).suffix.lower()
        ff = self.read_gerber_file_function(path).lower()
        altium_desc = self.read_altium_extrep_description(path).lower()

        ignore_exts = tuple(CAM_METADATA_EXTS | {".drr", ".log", ".lst", ".rpt"})
        if raw.endswith(ignore_exts):
            return "ignore"
        if any(k in n for k in ("status_report", "transcode_report", "readme", "read_me", "gerber_job", "job_file")) and ext in {".txt", ".rep", ".gbrjob"}:
            return "ignore"

        if self.is_drill(path):
            return "drill"

        def role_from_text(t: str) -> str:
            t = t.lower().replace("-", "_").replace(" ", "_")
            # drill maps are graphical documentation, not Excellon drill holes
            if any(k in t for k in ("drill_drawing", "drilldrawing", "drill_map", "drillmap", "drill_guide", "drillguide", "drill_legend", "hole_chart")):
                return "drillmap"
            if any(k in t for k in ("paste", "cream", "solder_paste", "pastemask", "paste_mask", "stencil")):
                return "paste"
            if any(k in t for k in ("soldermask", "solder_mask", "solderresist", "solder_resist", "resist", "stopmask", "stop_mask", "tstop", "bstop", "mask")):
                return "mask"
            if any(k in t for k in ("silkscreen", "silk_screen", "silk", "legend", "overlay", "ident", "component_print", "placement", "tplace", "bplace", "tsilk", "bsilk")):
                return "silk"
            if any(k in t for k in ("assembly", "assy", "fabdrawing", "fab_drawing", "fabrication_drawing")):
                return "assembly"
            if any(k in t for k in ("profile", "edge_cuts", "edgecuts", "board_outline", "boardoutline", "outline", "dimension", "route", "routing", "milling", "mechanical", "keepout", "keep_out", "contour", "gko")):
                return "mechanical"
            if any(k in t for k in ("pad_master", "padmaster", "pads_master", "pads")):
                return "pads"
            if any(k in t for k in ("copper", "toplayer", "bottomlayer", "top_layer", "bottom_layer", "signal", "plane", "midlayer", "mid_layer", "internalplane", "internal_plane", "innerlayer", "inner_layer")):
                return "copper"
            return ""

        if altium_desc:
            r = role_from_text(altium_desc)
            if r:
                return r

        if ff:
            f = ff.replace(" ", "").replace("_", "").lower()
            if "copper" in f:
                return "copper"
            if "soldermask" in f or "mask" in f:
                return "mask"
            if "paste" in f:
                return "paste"
            if "legend" in f or "silkscreen" in f or "silk" in f:
                return "silk"
            if "profile" in f or "edge" in f or "outline" in f:
                return "mechanical"
            if "drill" in f:
                return "drill"

        ext_map = {
            # Standard / fab-house
            ".gtl": "copper", ".gbl": "copper",
            ".g1": "copper", ".g2": "copper", ".g3": "copper", ".g4": "copper", ".g5": "copper", ".g6": "copper",
            ".l1": "copper", ".l2": "copper", ".l3": "copper", ".l4": "copper", ".l5": "copper", ".l6": "copper",
            ".gp1": "copper", ".gp2": "copper", ".gp3": "copper", ".gp4": "copper",
            ".gts": "mask", ".gbs": "mask", ".smt": "mask", ".smb": "mask", ".stc": "mask", ".sts": "mask",
            ".gtp": "paste", ".gbp": "paste", ".spt": "paste", ".spb": "paste", ".crc": "paste", ".crs": "paste",
            ".gto": "silk", ".gbo": "silk", ".sst": "silk", ".ssb": "silk", ".plc": "silk", ".pls": "silk",
            ".gpt": "pads", ".gpb": "pads",
            ".gko": "mechanical", ".gm1": "mechanical", ".gm2": "mechanical", ".gm3": "mechanical", ".gm4": "mechanical", ".gml": "mechanical", ".oln": "mechanical", ".dim": "mechanical", ".out": "mechanical",
            # Eagle
            ".cmp": "copper", ".sol": "copper",
            # Proteus/PADS/DipTrace sometimes use TOP/BOT as Gerber extensions
            ".top": "copper", ".bot": "copper",
        }
        if ext in ext_map:
            return ext_map[ext]

        r = role_from_text(n)
        if r:
            return r

        # Ambiguous .gbr/.ger/.pho/.art files: content/X2 did not say; use last-resort name tokens.
        if re.search(r"(^|_)(f|front|component|comp|top|primary)(_)?(cu|copper|layer|sig|signal)?($|_)", n):
            return "copper"
        if re.search(r"(^|_)(b|back|solder|bottom|secondary)(_)?(cu|copper|layer|sig|signal)?($|_)", n):
            return "copper"
        if re.search(r"(^|_)(in|inner|internal|mid|plane|power|gnd|vcc)\d*($|_)", n):
            return "copper"

        return "generic"

    def is_drill(self, path: str) -> bool:
        n, e = Path(path).name.lower(), Path(path).suffix.lower()

        gerber_exts = GERBER_EXTS
        if e in gerber_exts:
            return False

        if e in DRILL_EXTS:
            return True

        if e == ".txt":
            try:
                head = Path(path).read_text(errors="ignore")[:800].upper()
                return head.lstrip().startswith("M48") or re.search(r"(^|\n)T\d+(?:F\d+S\d+)?C", head) is not None
            except Exception:
                return False

        return False

    def open_files(self):
        files, _ = QFileDialog.getOpenFileNames(
            self,
            "Open CAM files",
            "",
            "CAM/Gerber/Drill (*.gbr *.ger *.pho *.art *.gtl *.gbl *.g1 *.g2 *.g3 *.g4 *.gp1 *.gp2 *.gpb *.gpt *.gtp *.gts *.gbs *.gto *.gbo *.gbp *.gko *.gm1 *.gm2 *.gml *.drl *.xln *.nc *.tap *.ncd *.nct *.exc *.txt *.sol *.cmp *.stc *.sts *.crc *.crs *.plc *.pls *.top *.bot *.smt *.smb *.sst *.ssb *.spt *.spb *.l1 *.l2 *.l3 *.l4 *.out *.oln *.dim *.zip);;All files (*)"
        )
        if files:
            self.load_files(files)

    def open_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Open CAM folder")
        if not folder:
            return
        files = self.collect_cam_files(folder)
        if files:
            self.load_files(files)

    @staticmethod
    def collect_cam_files(folder: str) -> List[str]:
        """Collect CAM files recursively.

        Many exported jobs arrive as a ZIP/folder containing a parent directory
        (for example PCB/...) and the old code only scanned the first directory
        level.  That made valid layers such as GP1/GP2 appear to be missing.
        """
        root = Path(folder)
        exts = CAM_OPEN_EXTS
        files = [str(p) for p in sorted(root.rglob("*")) if p.is_file() and p.suffix.lower() in exts]
        if not files:
            files = [str(p) for p in sorted(root.rglob("*")) if p.is_file() and 0 < p.stat().st_size < 200_000_000]
        return files

    def expand_input_files(self, files: List[str]) -> List[str]:
        """Expand ZIP CAM jobs and return the real renderable files.

        Keeps extracted temporary folders alive for the lifetime of the app, so
        layer paths remain readable after loading.
        """
        expanded: List[str] = []
        if not hasattr(self, "_zip_temp_dirs"):
            self._zip_temp_dirs = []

        for f in files:
            path = Path(f)
            if path.suffix.lower() == ".zip":
                try:
                    tmp = tempfile.TemporaryDirectory(prefix="ultra_gviewer_zip_")
                    self._zip_temp_dirs.append(tmp)
                    with zipfile.ZipFile(path, "r") as z:
                        z.extractall(tmp.name)
                    cam_files = self.collect_cam_files(tmp.name)
                    expanded.extend(cam_files)
                    self.log_msg(f"ZIP expanded: {path.name} -> {len(cam_files)} CAM file(s)")
                except Exception as e:
                    self.log_msg(f"ZIP ERROR {path.name}: {type(e).__name__}: {e}")
                continue
            expanded.append(str(path))

        seen = set()
        out: List[str] = []
        for f in expanded:
            key = str(Path(f).resolve()).lower()
            if key not in seen:
                seen.add(key)
                out.append(f)
        return out

    def load_files(self, files: List[str]):
        files = self.expand_input_files(files)
        self.log_msg(f"Loading {len(files)} file(s)...")
        for f in files:
            if any(Path(l.path) == Path(f) for l in self.layers):
                continue

            name = Path(f).name
            layer_type = self.classify_layer_type(f)

            if layer_type == "ignore":
                self.log_msg(f"IGNORED non-render layer: {name}")
                continue

            color = self.default_layer_color(name, layer_type)

            try:
                if self.is_drill(f):
                    drill_parser = ExcellonParser()
                    prims = drill_parser.parse_file(f)
                    info = f"DRILL prim={len(prims)} {drill_parser.info}"
                else:
                    head = Path(f).read_text(errors="ignore")[:250000]
                    if LegacyAltiumGerberParser().detect_legacy_altium_mode(f, head):
                        parser = LegacyAltiumGerberParser()
                    else:
                        parser = GerberParser()
                    prims = parser.parse_file(f)
                    d = parser.debug
                    legacy_tag = " LEGACY_ALTIUM" if getattr(parser, "legacy_altium_mode", False) else " MODERN_KICAD_V8"
                    img_pol_tag = f" IP={getattr(parser, 'image_polarity', 'positive')}"
                    info = f"GERBER{legacy_tag}{img_pol_tag} prim={len(prims)} cmd={d['cmd']} ap={d['ap']} draw={d['draw']} flash={d['flash']} reg={d['region']} fb={d['fallback']} FS={parser.x_int}.{parser.x_dec} {parser.unit}"

                layer_side = self.layer_side_from_file(f)
                default_visible = self.default_layer_visible(f, layer_type)
                cad_family = self.detect_cad_family(f)
                layer = Layer(name=name, path=f, color=color, primitives=prims, visible=default_visible, info=f"{cad_family.upper()} | {layer_type.upper()} / {layer_side.upper()} | {info}")
                setattr(layer, "layer_type", layer_type)
                setattr(layer, "layer_side", layer_side)
                setattr(layer, "file_function", self.read_gerber_file_function(f))
                setattr(layer, "cad_family", self.detect_cad_family(f))
                if not self.is_drill(f):
                    setattr(layer, "image_polarity", getattr(parser, "image_polarity", "positive"))
                    setattr(layer, "legacy_altium_mode", getattr(parser, "legacy_altium_mode", False))
                self.layers.append(layer)
                self.add_row(layer)
                self.log_msg(f"OK {name}: {info}")

            except Exception as e:
                self.log_msg(f"ERROR {name}: {type(e).__name__}: {e}")
                self.log_msg(traceback.format_exc(limit=2))

        self.auto_align_outside_drill_layers()
        self.render_visible()


    def auto_align_outside_drill_layers(self):
        """Auto-correct real Excellon drill hit layers by registration, not by bbox center.

        The previous fix translated a wrong-origin drill cloud to the board bbox center.
        That is too crude: a connector-heavy PCB often has drill hits only on one side,
        so its bbox center is *not* the board center.  This version extracts pad/via
        centres from copper/pad layers and finds the translation that makes the most
        drill centres coincide with real copper pad centres.  TXT Excellon files are
        allowed here; only documentation/table-like TXT layers are ignored when they
        do not contain a normal drill cloud.
        """
        if len(self.layers) < 2:
            return

        board_ref = self.renderer.main_board_reference(self.layers).normalized()
        if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
            return

        board_span = max(board_ref.width(), board_ref.height(), 1.0)
        board_ext = QRectF(board_ref).adjusted(-8.0, -8.0, 8.0, 8.0)

        def prim_center_and_size(prim: Primitive):
            try:
                if prim.kind == "circle" and prim.points:
                    c = prim.points[0]
                    return c.x(), c.y(), max(float(prim.radius) * 2.0, 0.001)
                if prim.kind in ("rect", "obround") and prim.points:
                    c = prim.points[0]
                    w, h = prim.rect or (0.2, 0.2)
                    return c.x(), c.y(), max(float(w), float(h), 0.001)
                if prim.kind == "polygon" and len(prim.points) >= 3:
                    r = QPolygonF(prim.points).boundingRect().normalized()
                    if r.isValid():
                        return r.center().x(), r.center().y(), max(r.width(), r.height(), 0.001)
            except Exception:
                return None
            return None

        # Pad/via targets.  Do not use line centres; tracks would create false matches.
        pad_targets = []
        for layer in self.layers:
            if not layer.visible:
                continue
            if str(getattr(layer, "layer_type", "")).lower() == "drill":
                continue
            lname = layer.name.lower()
            if not any(k in lname for k in ("copper", "pads", "signal", "top", "bottom")):
                continue
            if self.renderer.is_wireframe_visual_layer_name(lname):
                continue
            for prim in layer.primitives:
                cs = prim_center_and_size(prim)
                if cs is None:
                    continue
                x, y, size = cs
                if size < 0.08 or size > 8.0:
                    continue
                if not board_ext.contains(QPointF(x, y)):
                    continue
                pad_targets.append((x, y, size))

        if len(pad_targets) < 6:
            return

        # Spatial hash for fast nearest-pad tests.
        cell = 0.25
        grid = {}
        for x, y, size in pad_targets:
            key = (int(round(x / cell)), int(round(y / cell)))
            grid.setdefault(key, []).append((x, y, size))

        def has_target(x, y, drill_dia):
            gx, gy = int(round(x / cell)), int(round(y / cell))
            tol = max(0.13, min(0.45, drill_dia * 0.80))
            tol2 = tol * tol
            for ix in range(gx - 2, gx + 3):
                for iy in range(gy - 2, gy + 3):
                    for px, py, psz in grid.get((ix, iy), ()):  # small local bucket
                        # Pad must be at least comparable to the hole.
                        if psz + 0.20 < drill_dia:
                            continue
                        dx = x - px
                        dy = y - py
                        if dx * dx + dy * dy <= tol2:
                            return True
            return False

        def is_real_drill_cloud(layer: Layer, drills: list) -> bool:
            if len(drills) >= 3:
                return True
            # A true drill table/report usually contains long drawing geometry, not only flashes.
            base = layer.name.lower()
            report_words = ("read", "legend", "table", "chart", "map", "report")
            return not any(w in base for w in report_words)

        def move_layer(layer: Layer, dx: float, dy: float):
            def move_pt(pt: QPointF):
                pt.setX(pt.x() + dx)
                pt.setY(pt.y() + dy)

            for prim in layer.primitives:
                for pt in getattr(prim, "points", []) or []:
                    move_pt(pt)
                for contour in getattr(prim, "contours", None) or []:
                    for pt in contour:
                        move_pt(pt)
                for attr in (
                    "_fast_path_cache", "_solid_stroke_cache", "_solid_stroke_cache_key",
                    "_fast_region_path_cache", "_fast_polygon_cache"
                ):
                    if hasattr(prim, attr):
                        delattr(prim, attr)
            for attr in ("_fast_bounds_cache", "_viewport_candidate_cache"):
                if hasattr(layer, attr):
                    delattr(layer, attr)
            layer.bbox = self.renderer.layer_bounds(layer)

        for layer in self.layers:
            if str(getattr(layer, "layer_type", "")).lower() != "drill":
                continue

            drills = []
            for prim in layer.primitives:
                if prim.kind == "circle" and prim.points:
                    c = prim.points[0]
                    drills.append((c.x(), c.y(), max(float(prim.radius) * 2.0, 0.05)))
                elif prim.kind == "line" and len(prim.points) >= 2:
                    p1, p2 = prim.points[0], prim.points[1]
                    drills.append((p1.x(), p1.y(), max(float(prim.width), 0.05)))
                    drills.append((p2.x(), p2.y(), max(float(prim.width), 0.05)))

            if not is_real_drill_cloud(layer, drills):
                continue

            b = self.renderer.layer_bounds(layer).normalized()
            if not b.isValid() or b.width() <= 0 or b.height() <= 0:
                continue

            # Generate candidate translations from drill->pad pairs.  Quantizing
            # collapses thousands of similar offsets into one robust vote bucket.
            sample_drills = drills[:120]
            sample_targets = pad_targets[:2500]
            q = 0.02
            votes = {}
            for dx0, dy0, dd in sample_drills:
                for px, py, psz in sample_targets:
                    if psz + 0.20 < dd:
                        continue
                    dx = px - dx0
                    dy = py - dy0
                    # Reject absurd shifts that would throw the cloud far away.
                    if abs(dx) > board_span * 4.0 or abs(dy) > board_span * 4.0:
                        continue
                    key = (round(dx / q), round(dy / q))
                    votes[key] = votes.get(key, 0) + 1

            if not votes:
                continue

            # Score only the strongest offset hypotheses.
            best = None
            for key, _ in sorted(votes.items(), key=lambda kv: kv[1], reverse=True)[:80]:
                dx = key[0] * q
                dy = key[1] * q
                hits = 0
                for x, y, dd in drills:
                    if has_target(x + dx, y + dy, dd):
                        hits += 1
                ratio = hits / max(len(drills), 1)
                # Prefer more matches; secondarily prefer smaller movement.
                score = (hits, ratio, -math.hypot(dx, dy))
                if best is None or score > best[0]:
                    best = (score, dx, dy, hits, ratio)

            if best is None:
                continue

            _, dx, dy, hits, ratio = best
            already_hits = sum(1 for x, y, dd in drills if has_target(x, y, dd))
            min_hits = max(5, min(18, int(len(drills) * 0.10)))

            # Apply only when it is clearly better than current placement.
            if hits < min_hits or hits <= already_hits + 3:
                continue
            if abs(dx) < 0.03 and abs(dy) < 0.03:
                continue

            move_layer(layer, dx, dy)
            layer.info = f"PAD-MATCHED DRILL dx={dx:.3f} dy={dy:.3f} mm hits={hits}/{len(drills)} | " + layer.info
            self.log_msg(f"PAD-MATCHED drill layer {layer.name}: dx={dx:.3f} mm dy={dy:.3f} mm hits={hits}/{len(drills)}")

            for r in range(self.table.rowCount()):
                item = self.table.item(r, 2)
                if item and item.data(Qt.ItemDataRole.UserRole) is layer:
                    info_item = self.table.item(r, 3)
                    if info_item:
                        info_item.setText(layer.info)
                    break

    def add_row(self, layer: Layer):
        self._block_table = True
        r = self.table.rowCount()
        self.table.insertRow(r)

        on = QTableWidgetItem()
        on.setFlags(Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable)
        on.setCheckState(Qt.CheckState.Checked if layer.visible else Qt.CheckState.Unchecked)
        self.table.setItem(r, 0, on)

        col = QTableWidgetItem("")
        col.setFlags(Qt.ItemFlag.ItemIsEnabled | Qt.ItemFlag.ItemIsSelectable)
        col.setForeground(QBrush(layer.color))
        col.setBackground(QBrush(QColor(11, 23, 40)))
        col.setData(Qt.ItemDataRole.UserRole, layer)
        self.table.setItem(r, 1, col)

        name = QTableWidgetItem(layer.name)
        name.setData(Qt.ItemDataRole.UserRole, layer)
        self.table.setItem(r, 2, name)

        info = QTableWidgetItem(layer.info)
        info.setData(Qt.ItemDataRole.UserRole, layer)
        self.table.setItem(r, 3, info)

        side = getattr(layer, "layer_side", "unknown")
        typ = getattr(layer, "layer_type", "generic")
        group_bg = QColor(11, 23, 40)
        if side == "top":
            group_bg = QColor(37, 31, 11)
        elif side == "bottom":
            group_bg = QColor(39, 14, 28)
        elif side == "both":
            group_bg = QColor(14, 34, 32)
        elif side == "inner":
            group_bg = QColor(28, 20, 48)
        if typ in {"mechanical", "drill"}:
            group_bg = QColor(14, 34, 32)

        full_path = str(Path(layer.path))
        tooltip = (
            f"Full file: {Path(layer.path).name}\n"
            f"Full path: {full_path}\n"
            f"CAD: {getattr(layer, 'cad_family', 'generic')}\n"
            f"Type: {typ}\n"
            f"Side: {side}\n"
            f"FileFunction: {getattr(layer, 'file_function', '')}"
        )
        for c in range(self.table.columnCount()):
            it = self.table.item(r, c)
            if it:
                if c in (2, 3):
                    it.setBackground(QBrush(group_bg))
                it.setToolTip(tooltip)

        self._block_table = False

    def layer_for_row(self, row: int) -> Optional[Layer]:
        item = self.table.item(row, 2)
        return item.data(Qt.ItemDataRole.UserRole) if item else None

    def table_changed(self, item: QTableWidgetItem):
        if self._block_table or item.column() != 0:
            return
        layer = self.layer_for_row(item.row())
        if layer:
            layer.visible = item.checkState() == Qt.CheckState.Checked
            self.render_visible(preserve_view=False)

    def set_all(self, state: bool):
        self._block_table = True
        for r in range(self.table.rowCount()):
            layer = self.layer_for_row(r)
            if layer:
                layer.visible = state
            self.table.item(r, 0).setCheckState(Qt.CheckState.Checked if state else Qt.CheckState.Unchecked)
        self._block_table = False
        self.render_visible(preserve_view=False)

    def select_layer_row(self, layer: Layer):
        """Select and light up the row in the left Layers table for a picked layer."""
        if layer is None:
            return
        for r in range(self.table.rowCount()):
            if self.layer_for_row(r) is layer:
                self.table.blockSignals(True)
                self.table.clearSelection()
                self.table.selectRow(r)
                self.table.setCurrentCell(r, 2)
                self.table.scrollToItem(self.table.item(r, 2), QAbstractItemView.ScrollHint.PositionAtCenter)
                self.table.blockSignals(False)
                self.update_pick_layers()
                return

    def selected_layers(self) -> List[Layer]:
        rows = sorted({i.row() for i in self.table.selectedIndexes()})
        return [self.layer_for_row(r) for r in rows if self.layer_for_row(r)]

    def highlight_from_table(self):
        layers = self.selected_layers()
        if not layers:
            return

        layer = layers[0]
        if self.canvas.highlight and self.canvas.highlight[0] is layer:
            self.canvas.highlight = None
        else:
            self.canvas.highlight = (layer, None)

        self.canvas.set_active_pick_layers(layers)
        self.canvas.update()

    def update_pick_layers(self):
        self.canvas.set_active_pick_layers(self.selected_layers())

    def change_color(self):
        layers = self.selected_layers()

        if not layers and self.canvas.highlight:
            layers = [self.canvas.highlight[0]]

        if not layers:
            for r in range(self.table.rowCount()):
                layer = self.layer_for_row(r)
                if layer and layer.visible:
                    layers = [layer]
                    self.table.selectRow(r)
                    break

        if not layers:
            self.log_msg("Change Color: no layer selected.")
            return

        layer = layers[0]
        col = QColorDialog.getColor(layer.color, self, f"Layer color - {layer.name}")
        if not col.isValid():
            return

        col.setAlpha(230)
        layer.color = col

        for r in range(self.table.rowCount()):
            if self.layer_for_row(r) is layer:
                item = self.table.item(r, 1)
                if item:
                    item.setForeground(QBrush(col))
                    item.setBackground(QBrush(QColor(11, 23, 40)))
                    item.setText("")
                    self.table.viewport().update()

        if self.canvas.highlight and self.canvas.highlight[0] is layer:
            self.canvas.highlight = (layer, self.canvas.highlight[1])

        self.render_visible()
        self.log_msg(f"Changed color: {layer.name}")


    def use_all_layer_colors(self):
        """Re-apply the full palette to every loaded layer and repaint the table/canvas."""
        for r in range(self.table.rowCount()):
            layer = self.layer_for_row(r)
            if not layer:
                continue

            col = QColor(self.COLORS[r % len(self.COLORS)])
            lname = layer.name.lower()
            if any(k in lname for k in ("assembly", "3d", "drillmap", "mechanical", "drawing", "courtyard")):
                col.setAlpha(150)
            elif "mask" in lname:
                col.setAlpha(95)
            elif "paste" in lname:
                col.setAlpha(135)
            else:
                col.setAlpha(235)

            layer.color = col

            item = self.table.item(r, 1)
            if item:
                item.setForeground(QBrush(col))
                item.setBackground(QBrush(QColor(11, 23, 40)))
                item.setText("")
                item.setData(Qt.ItemDataRole.UserRole, layer)

        self.table.viewport().update()
        self.render_visible(preserve_view=True)
        self.log_msg("Applied full layer color palette.")

    def rect_distance_mm(self, a: QRectF, b: QRectF) -> float:
        """Distance between two rectangles in mm; 0 when they intersect."""
        a = QRectF(a).normalized()
        b = QRectF(b).normalized()
        if not a.isValid() or not b.isValid():
            return 0.0
        if a.intersects(b):
            return 0.0
        dx = 0.0
        if a.right() < b.left():
            dx = b.left() - a.right()
        elif b.right() < a.left():
            dx = a.left() - b.right()
        dy = 0.0
        if a.bottom() < b.top():
            dy = b.top() - a.bottom()
        elif b.bottom() < a.top():
            dy = a.top() - b.bottom()
        return math.hypot(dx, dy)

    def update_layer_camera_diagnostics(self):
        """Update the left table with FIT/camera diagnostics without hiding layers.

        Meaning:
          OK/CAMERA: real PCB layer that participates in FIT.
          OK/VISIBLE: helper layer close to the PCB; visible but does not drive FIT.
          CAMERA-IGNORED: helper/chart/assembly layer; visible as WIREFRAME, excluded from FIT by design.
          OUTSIDE: geometry exists far away from the PCB reference and is clipped/ignored for camera.
        """
        if not self.layers:
            return

        board_ref = self.renderer.main_board_reference(self.layers)
        if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
            return

        board_span = max(board_ref.width(), board_ref.height(), 1.0)
        board_expanded = QRectF(board_ref).adjusted(-20, -20, 20, 20)
        visible_count = sum(1 for l in self.layers if l.visible)

        self._block_table = True
        try:
            for r in range(self.table.rowCount()):
                layer = self.layer_for_row(r)
                if not layer:
                    continue
                b = self.renderer.layer_bounds(layer).normalized()
                layer.bbox = b
                old_info = layer.info
                for prefix in (
                    "OK/CAMERA | ", "OK/VISIBLE | ", "OK/SOLO | ", "CAMERA-IGNORED | ",
                    "OUTSIDE | ", "EMPTY | ", "CHECK-POSITION | "
                ):
                    if old_info.startswith(prefix):
                        old_info = old_info[len(prefix):]
                        break

                if not b.isValid() or b.width() <= 0 or b.height() <= 0:
                    diag = "EMPTY"
                    color = QColor(120, 120, 120)
                    tip = "No drawable geometry was parsed from this file."
                else:
                    dist = self.rect_distance_mm(b, board_expanded)
                    span = max(b.width(), b.height())
                    is_helper = self.renderer.is_helper_camera_layer_name(layer.name)
                    is_camera = self.renderer.is_board_camera_layer_name(layer.name)

                    if layer.visible and visible_count == 1:
                        diag = "OK/SOLO"
                        color = QColor(90, 225, 255)
                        tip = "This is the only visible layer, so FIT/camera is based on this layer alone."
                    elif is_camera and dist <= max(12.0, board_span * 0.15) and span <= max(250.0, board_span * 3.0):
                        diag = "OK/CAMERA"
                        color = QColor(30, 210, 110)
                        tip = "This real PCB fabrication layer participates in FIT/camera."
                    elif dist <= max(25.0, board_span * 0.30) and span <= max(350.0, board_span * 4.0):
                        diag = "OK/VISIBLE"
                        color = QColor(255, 190, 60)
                        tip = "Visible layer near the PCB. This is a normal documentation/mechanical overlay, not a placement error."
                    elif is_helper:
                        diag = "CAMERA-IGNORED"
                        color = QColor(255, 140, 60)
                        tip = (
                            "This helper/annotation layer has geometry away from the PCB. "
                            "It remains loaded and checked, but it is ignored for FIT/camera."
                        )
                    else:
                        diag = "OUTSIDE"
                        color = QColor(255, 70, 90)
                        tip = (
                            "This layer bbox is far from the PCB reference. Check units/format/origin. "
                            "It remains loaded, but it is not allowed to destroy the camera bbox."
                        )

                    tip += f"\nLayer bbox: x={b.x():.3f} y={b.y():.3f} w={b.width():.3f} h={b.height():.3f} mm"
                    tip += f"\nPCB ref: x={board_ref.x():.3f} y={board_ref.y():.3f} w={board_ref.width():.3f} h={board_ref.height():.3f} mm"

                full_path = str(Path(layer.path))
                full_name = Path(layer.path).name
                meta_tip = (
                    f"Full file: {full_name}\n"
                    f"Full path: {full_path}\n"
                    f"CAD: {getattr(layer, 'cad_family', 'generic')}\n"
                    f"Type: {getattr(layer, 'layer_type', 'generic')}\n"
                    f"Side: {getattr(layer, 'layer_side', 'unknown')}\n"
                    f"FileFunction: {getattr(layer, 'file_function', '')}"
                )
                tip = meta_tip + "\n\n" + tip

                layer.info = f"{diag} | {old_info}"
                for c in range(self.table.columnCount()):
                    it = self.table.item(r, c)
                    if it:
                        it.setToolTip(tip)
                        if c == 3:
                            it.setText(layer.info)
                            it.setForeground(color)
                        elif c == 2 and diag in ("CAMERA-IGNORED", "OUTSIDE", "CHECK-POSITION"):
                            it.setForeground(color)
        finally:
            self._block_table = False

    def render_visible(self, preserve_view: bool = False):
        if not any(l.visible for l in self.layers):
            self.canvas.pixmap = None
            self.canvas.update()
            return

        self.log_msg("Rendering visible layers internally...")
        try:
            img = self.renderer.render(self.layers)

            if not any(l.visible for l in self.layers):
                for l in self.layers:
                    l.visible = True
                for r in range(self.table.rowCount()):
                    item = self.table.item(r, 0)
                    if item:
                        item.setCheckState(Qt.CheckState.Checked)
                img = self.renderer.render(self.layers)

        except Exception as e:
            self.log_msg(f"RENDER ERROR: {type(e).__name__}: {e}")
            self.log_msg(traceback.format_exc(limit=4))
            return
        self.canvas.set_image(img, preserve_view=(preserve_view and self.canvas.pixmap is not None))
        self.canvas.set_scene(self.layers, self.renderer.last_world_bounds, self.renderer.last_px_per_mm, self.renderer.margin_px)
        self.update_layer_camera_diagnostics()
        self.update_pick_layers()

        b = self.renderer.last_world_bounds
        self.log_msg(f"Rendered image {img.width()}x{img.height()} px | world bbox x={b.x():.3f} y={b.y():.3f} w={b.width():.3f} h={b.height():.3f} mm")

    def export_png(self, side: Optional[str] = None):
        """Export a realistic TOP/BOTTOM PCB PNG from the visible fabrication layers.

        This is not a widget screenshot. It renders the CAM primitives directly
        into a fresh high-resolution QImage, so the exported PNG keeps the same
        geometry, colors, antialiasing and layer visibility logic as the viewer.
        """
        if not self.layers:
            self.log_msg("Export PNG: no Gerber/Drill layers loaded.")
            return

        if not any(layer.visible for layer in self.layers):
            self.log_msg("Export PNG: no visible layers. Turn at least one layer ON.")
            return

        export_side = (side or self.renderer.auto_realistic_png_side(self.layers)).lower()
        suggested_name = f"ultra_gerber_{export_side}_realistic.png"
        visible_names = [Path(layer.name).stem for layer in self.layers if layer.visible]
        if len(visible_names) == 1 and visible_names[0]:
            suggested_name = f"{visible_names[0]}_export.png"

        path, _ = QFileDialog.getSaveFileName(
            self,
            "Export visible Gerber layers to PNG",
            suggested_name,
            "PNG Image (*.png)"
        )
        if not path:
            return
        if not path.lower().endswith(".png"):
            path += ".png"

        if export_side in ("bottom", "bot", "b", "kbottom", "kicad_bottom", "b.cu"):
            self.log_msg("Export PNG: rendering realistic BOTTOM side image with single CAM transform mirror...")
        else:
            self.log_msg(f"Export PNG: rendering realistic {export_side.upper()} side image from Gerber/Drill layers...")

        try:
            img, export_renderer = self._render_export_image(side=export_side)
            if img.isNull() or img.width() <= 0 or img.height() <= 0:
                self.log_msg("Export PNG ERROR: rendered image is empty.")
                return

            ok = img.save(path, "PNG")
            if not ok:
                self.log_msg(f"Export PNG ERROR: could not save file: {path}")
                return

            b = export_renderer.last_world_bounds
            self.log_msg(
                f"Exported PNG: {path} | {img.width()}x{img.height()} px | "
                f"bbox x={b.x():.3f} y={b.y():.3f} w={b.width():.3f} h={b.height():.3f} mm"
            )
        except Exception as e:
            self.log_msg(f"Export PNG ERROR: {type(e).__name__}: {e}")
            self.log_msg(traceback.format_exc(limit=6))

    def _render_export_image(self, side: str = "top") -> tuple[QImage, RasterRenderer]:
        """Render realistic PCB PNG for exactly one physical PCB side.

        Bottom-side PNG exports are mirrored once inside RasterRenderer.render_realistic()
        by using the painter world transform. There is intentionally no final
        QImage.mirrored() step here, because that caused double-mirror failures
        when bottom layers were already transformed correctly.
        """
        export_renderer = RasterRenderer()
        export_renderer.px_per_mm = 70.0
        export_renderer.max_side = 14000
        export_renderer.margin_px = 140

        export_side = (side or "top").strip().lower()
        img = export_renderer.render_realistic(self.layers, side=export_side)

        return img, export_renderer

    def _render_export_pdf_image(self) -> tuple[QImage, RasterRenderer]:
        """Render black/white PDF from exactly the visible selected layers."""
        export_renderer = RasterRenderer()
        export_renderer.px_per_mm = 55.0
        export_renderer.max_side = 10000
        export_renderer.margin_px = 90
        img = export_renderer.render_monochrome(self.layers)
        return img, export_renderer

    def export_pdf(self):
        """Export the currently visible Gerber/Drill layers to a single-page PDF."""
        if not self.layers:
            self.log_msg("Export PDF: no Gerber/Drill layers loaded.")
            return

        if not any(layer.visible for layer in self.layers):
            self.log_msg("Export PDF: no visible layers. Turn at least one layer ON.")
            return

        suggested_name = "ultra_gerber_export.pdf"
        visible_names = [Path(layer.name).stem for layer in self.layers if layer.visible]
        if len(visible_names) == 1 and visible_names[0]:
            suggested_name = f"{visible_names[0]}_export.pdf"

        path, _ = QFileDialog.getSaveFileName(
            self,
            "Export visible Gerber layers to PDF",
            suggested_name,
            "PDF File (*.pdf)"
        )
        if not path:
            return
        if not path.lower().endswith(".pdf"):
            path += ".pdf"

        self.log_msg("Export PDF: rendering visible layers to PDF...")

        try:
            img, export_renderer = self._render_export_pdf_image()
            if img.isNull() or img.width() <= 0 or img.height() <= 0:
                self.log_msg("Export PDF ERROR: rendered image is empty.")
                return

            pdf = QPdfWriter(path)
            pdf.setCreator("ULTRA GERBER VIEWER by George Kourtidis")
            pdf.setTitle("Gerber export")
            pdf.setResolution(300)

            orientation = (
                QPageLayout.Orientation.Landscape
                if img.width() >= img.height()
                else QPageLayout.Orientation.Portrait
            )
            page_layout = QPageLayout(
                QPageSize(QPageSize.PageSizeId.A4),
                orientation,
                QMarginsF(8.0, 8.0, 8.0, 8.0),
                QPageLayout.Unit.Millimeter
            )
            pdf.setPageLayout(page_layout)

            painter = QPainter(pdf)
            if not painter.isActive():
                self.log_msg(f"Export PDF ERROR: could not open PDF writer: {path}")
                return

            page_rect = QRectF(pdf.pageLayout().paintRectPixels(pdf.resolution()))
            img_ratio = img.width() / max(1, img.height())
            page_ratio = page_rect.width() / max(1.0, page_rect.height())

            if img_ratio >= page_ratio:
                target_w = page_rect.width()
                target_h = target_w / img_ratio
            else:
                target_h = page_rect.height()
                target_w = target_h * img_ratio

            target = QRectF(
                page_rect.left() + (page_rect.width() - target_w) / 2.0,
                page_rect.top() + (page_rect.height() - target_h) / 2.0,
                target_w,
                target_h
            )

            painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
            painter.drawImage(target, img, QRectF(img.rect()))
            painter.end()

            b = export_renderer.last_world_bounds
            self.log_msg(
                f"Exported PDF: {path} | source {img.width()}x{img.height()} px | "
                f"bbox x={b.x():.3f} y={b.y():.3f} w={b.width():.3f} h={b.height():.3f} mm"
            )
        except Exception as e:
            self.log_msg(f"Export PDF ERROR: {type(e).__name__}: {e}")
            self.log_msg(traceback.format_exc(limit=6))

    def clear_all(self):
        self.layers.clear()
        self.table.setRowCount(0)
        self.log.clear()
        self.canvas.pixmap = None
        self.canvas.layers = []
        self.canvas.active_pick_layers = []
        self.canvas.highlight = None
        self.canvas.invalidate_highlight_cache()
        self.canvas.update()
        self.status.setText("Cleared")


    def solo_selected_layer(self):
        """Show exactly one selected layer, centered and unclipped.

        This is the same practical workflow used by mature Gerber viewers:
        pick/activate a layer, hide the rest, inspect it alone, then restore.
        All files remain loaded; only checkbox visibility changes.
        """
        layers = self.selected_layers()
        if not layers:
            self.log_msg("Solo Selected: select one row in the Layers table first.")
            return

        target = layers[0]
        self._block_table = True
        try:
            for r in range(self.table.rowCount()):
                layer = self.layer_for_row(r)
                if not layer:
                    continue
                layer.visible = (layer is target)
                item = self.table.item(r, 0)
                if item:
                    item.setCheckState(Qt.CheckState.Checked if layer.visible else Qt.CheckState.Unchecked)
        finally:
            self._block_table = False

        self.canvas.highlight = (target, None)
        self.canvas.set_active_pick_layers([target])
        self.render_visible(preserve_view=False)
        self.log_msg(f"Solo layer: {target.name}")


    @staticmethod
    def layer_side_name(name: str) -> str:
        """Filename-only side detection with CAD/vendor naming aliases."""
        raw = Path(name).name.lower()
        n = MainWindow.normalized_cam_name(raw)
        ext = Path(raw).suffix.lower()

        # KiCad and X2-style names
        if re.search(r"(^|_)f_(cu|mask|paste|silkscreen|silks|silk)(_|$)", n):
            return "top"
        if re.search(r"(^|_)b_(cu|mask|paste|silkscreen|silks|silk)(_|$)", n):
            return "bottom"
        if re.search(r"(^|_)in\d+_cu(_|$)", n):
            return "inner"

        if ext in {".gtl", ".gts", ".gtp", ".gpt", ".gto", ".top", ".cmp", ".stc", ".crc", ".plc", ".smt", ".sst", ".spt", ".l1"}:
            return "top"
        if ext in {".gbl", ".gbs", ".gbp", ".gpb", ".gbo", ".bot", ".sol", ".sts", ".crs", ".pls", ".smb", ".ssb", ".spb"}:
            return "bottom"
        if ext in {".g1", ".g2", ".g3", ".g4", ".g5", ".g6", ".gp1", ".gp2", ".gp3", ".gp4", ".l2", ".l3", ".l4", ".l5", ".l6"}:
            # In most old 2-layer outputs .G1/.L1 can mean top, but if a job already
            # uses GTL/GBL then G1.. are usually inner. Keep explicit L1/TOP as top;
            # bare G1 is treated as inner to avoid mixing planes with top copper.
            return "inner"

        both_tokens = (
            "edge_cuts", "edgecuts", "profile", "board_outline", "boardoutline", "outline", "dimension", "dim", "route", "routing", "milling", "mechanical", "keepout", "keep_out", "contour",
            "pth", "npth", "roundholes", "slot_holes", "slotholes", "drill", "holes", "ncd", "xln"
        )
        if any(k in n for k in both_tokens):
            return "both"

        inner_tokens = ("inner", "internal", "internal_plane", "internalplane", "midlayer", "mid_layer", "plane", "power", "gnd", "vcc")
        if any(k in n for k in inner_tokens) or re.search(r"(^|_)(in|inner|internal|mid|plane)\d+(_|$)", n):
            return "inner"

        top_tokens = (
            # Generic / fab-house
            "toplayer", "top_layer", "top_copper", "copper_top", "top_signal", "signal_top", "component_side", "component", "front", "primary",
            # Altium/Protel
            "topoverlay", "top_overlay", "toppaste", "top_paste", "topsolder", "top_solder", "topmask", "top_mask",
            # Proteus/ARES
            "top_resist", "top_silk", "top_silkscreen", "top_paste", "top_copper",
            # EasyEDA/DipTrace/PADS/Eagle aliases
            "topsoldermasklayer", "topsilklayer", "toppastemasklayer", "toplayer", "topmask", "topsilk", "tstop", "tcream", "tplace", "tsilk", "smt", "sst", "spt",
            "_top_", "top_", "_top"
        )
        bottom_tokens = (
            "bottomlayer", "bottom_layer", "bottom_copper", "copper_bottom", "bottom_signal", "signal_bottom", "solder_side", "back", "secondary", "bottom", "bot",
            "bottomoverlay", "bottom_overlay", "bottompaste", "bottom_paste", "bottomsolder", "bottom_solder", "bottommask", "bottom_mask",
            "bottom_resist", "bottom_silk", "bottom_silkscreen",
            "bottomsoldermasklayer", "bottomsilklayer", "bottompastemasklayer", "bottomlayer", "bottommask", "bottomsilk", "bstop", "bcream", "bplace", "bsilk", "smb", "ssb", "spb",
            "_bottom_", "bottom_", "_bottom", "_bot_", "bot_", "_bot"
        )
        if any(k in n for k in top_tokens):
            return "top"
        if any(k in n for k in bottom_tokens):
            return "bottom"

        # Single-letter vendor tokens: only when separated, to avoid false positives.
        if re.search(r"(^|_)(f|top|comp|component|front)(_)(cu|copper|layer|mask|paste|silk|legend)", n):
            return "top"
        if re.search(r"(^|_)(b|bot|bottom|solder|back)(_)(cu|copper|layer|mask|paste|silk|legend)", n):
            return "bottom"

        return "unknown"

    def layer_side_from_file(self, path: str) -> str:
        """Primary side detector. Uses X2 TF.FileFunction first, sidecar reports second, filename third."""
        ff = self.read_gerber_file_function(path)
        if ff:
            f = ff.lower().replace(" ", "")
            if ",top" in f or f.endswith("top"):
                return "top"
            if ",bot" in f or ",bottom" in f or f.endswith("bot") or f.endswith("bottom"):
                return "bottom"
            if "copper,l1" in f:
                return "top"
            if re.search(r"copper,l[2-9]", f) and not (",top" in f or ",bot" in f or ",bottom" in f):
                return "inner"
            if any(k in f for k in ("profile", "drill", "np", "nonplated", "plated")):
                return "both"
        desc = self.read_altium_extrep_description(path).lower()
        if desc:
            d = desc.replace("-", "_").replace(" ", "_")
            if any(k in d for k in ("top", "component_side")):
                return "top"
            if any(k in d for k in ("bottom", "solder_side")):
                return "bottom"
            if any(k in d for k in ("mid", "inner", "internal_plane", "plane")):
                return "inner"
            if any(k in d for k in ("dimension", "notes", "keep", "profile", "outline", "drill")):
                return "both"
        return self.layer_side_name(path)

    def layer_side(self, layer: Layer) -> str:
        side = getattr(layer, "layer_side", "")
        if side:
            return side
        return self.layer_side_from_file(getattr(layer, "path", getattr(layer, "name", "")))

    @staticmethod
    def layer_type_from_info(layer: Layer) -> str:
        typ = getattr(layer, "layer_type", "")
        if typ:
            return typ

        raw = (getattr(layer, "info", "") or "").lower()
        if "[copper]" in raw or "copper" in raw:
            return "copper"
        if "[mask]" in raw or "soldermask" in raw or "solder mask" in raw or "mask" in raw:
            return "mask"
        if "[paste]" in raw or "paste" in raw:
            return "paste"
        if "[silk]" in raw or "silkscreen" in raw or "legend" in raw or "silk" in raw:
            return "silk"
        if "[profile]" in raw or "edge_cuts" in raw or "profile" in raw or "mechanical" in raw:
            return "mechanical"
        if "[drill]" in raw or "npth" in raw or "pth" in raw or "drill" in raw:
            return "drill"

        first = raw.split("|", 1)[0].strip()
        return first.split("/", 1)[0].strip()

    @staticmethod
    def default_layer_color(name: str, layer_type: str) -> QColor:
        """Stable CAM-like palette: top/bottom/inner/helper layers do not share confusing colors."""
        n = Path(name).name.lower()
        side = MainWindow.layer_side_name(n)

        if "profile" in n:
            return QColor(0, 255, 194, 245)
        if layer_type == "drill":
            return QColor(120, 220, 255, 225)
        if "copper_signal_top" in n or (layer_type == "copper" and side == "top"):
            return QColor(255, 208, 66, 225)
        if "copper_signal_bot" in n or (layer_type == "copper" and side == "bottom"):
            return QColor(255, 74, 128, 210)
        if "copper_plane" in n or side == "inner":
            return QColor(180, 160, 255, 135)
        if "pads" in n or layer_type == "pads":
            return QColor(0, 255, 194, 235)
        if layer_type == "mask":
            return QColor(40, 255, 120, 75)
        if layer_type == "paste":
            return QColor(255, 170, 60, 105)
        if layer_type == "silk":
            return QColor(255, 255, 210, 240)
        if layer_type in {"assembly", "3d", "drillmap"} or any(k in n for k in ("courtyard", "component", "designator", "drawing")):
            return QColor(120, 220, 255, 120)
        if layer_type == "mechanical":
            return QColor(220, 220, 220, 150)
        return QColor(150, 108, 255, 180)

    @staticmethod
    def default_layer_visible(name: str, layer_type: str) -> bool:
        """Clean default visibility, close to KiCad GerbView workflow.

        All layers are loaded and selectable in the table.  Only the practical
        board view is enabled initially, so Assembly/3D/Drillmap/Designator/
        random Mechanical annotation layers do not cover the copper.
        """
        n = Path(name).name.lower()

        if "profile" in n or "board_outline" in n or "edge_cuts" in n or "edgecuts" in n:
            return True

        if any(k in n for k in (
            "assembly", "3d_body", "3d", "drillmap", "drawing",
            "courtyard", "component_center", "component_outline",
            "designator", "mechanical_13", "mechanical_15"
        )):
            return False

        if layer_type in {"copper", "pads", "mask", "paste", "silk", "mechanical", "drill"}:
            return True

        return False

    def set_layer_visibility_by_predicate(self, predicate, label: str):
        """Common layer preset helper. Files stay loaded; only checkboxes change."""
        self._block_table = True
        try:
            for r in range(self.table.rowCount()):
                layer = self.layer_for_row(r)
                if not layer:
                    continue
                visible = bool(predicate(layer))
                layer.visible = visible
                item = self.table.item(r, 0)
                if item:
                    item.setCheckState(Qt.CheckState.Checked if visible else Qt.CheckState.Unchecked)
        finally:
            self._block_table = False
        first_visible_row = None
        for r in range(self.table.rowCount()):
            layer = self.layer_for_row(r)
            if layer and layer.visible:
                first_visible_row = r
                break
        if first_visible_row is not None:
            self.table.selectRow(first_visible_row)
        self.update_pick_layers()
        self.render_visible(preserve_view=False)
        self.log_msg(label)

    def top_view(self):
        """Top-side inspection: only top-side layers plus outline/drills; never bottom/inner."""
        def keep(layer: Layer) -> bool:
            side = self.layer_side(layer)
            typ = self.layer_type_from_info(layer)
            if typ in {"mechanical", "drill"} and side in {"both", "unknown"}:
                return True
            return side == "top" and typ in {"copper", "silk", "mask", "paste", "pads"}
        self.set_layer_visibility_by_predicate(keep, "Top View: only TOP copper/mask/paste/silk + outline/drills. Bottom/inner layers OFF.")

    def bottom_view(self):
        """Bottom-side inspection: only bottom-side layers plus outline/drills; never top/inner."""
        def keep(layer: Layer) -> bool:
            side = self.layer_side(layer)
            typ = self.layer_type_from_info(layer)
            if typ in {"mechanical", "drill"} and side in {"both", "unknown"}:
                return True
            return side == "bottom" and typ in {"copper", "silk", "mask", "paste", "pads"}
        self.set_layer_visibility_by_predicate(keep, "Bottom View: only BOTTOM copper/mask/paste/silk + outline/drills. Top/inner layers OFF.")

    def top_copper_only(self):
        """Show exactly what the user expects when checking top copper: F_Cu plus board references."""
        def keep(layer: Layer) -> bool:
            side = self.layer_side(layer)
            typ = self.layer_type_from_info(layer)
            return (typ == "copper" and side == "top") or typ in {"mechanical", "drill"}
        self.set_layer_visibility_by_predicate(keep, "Top Copper Only: only F_Cu + Edge_Cuts + PTH/NPTH. No B_Cu, no mask, no paste.")

    def bottom_copper_only(self):
        """Show exactly bottom copper: B_Cu plus board references."""
        def keep(layer: Layer) -> bool:
            side = self.layer_side(layer)
            typ = self.layer_type_from_info(layer)
            return (typ == "copper" and side == "bottom") or typ in {"mechanical", "drill"}
        self.set_layer_visibility_by_predicate(keep, "Bottom Copper Only: only B_Cu + Edge_Cuts + PTH/NPTH. No F_Cu, no mask, no paste.")

    def both_copper_view(self):
        """Show top + bottom copper plus board references. Mask/paste/silk stay off."""
        def keep(layer: Layer) -> bool:
            typ = self.layer_type_from_info(layer)
            side = self.layer_side(layer)
            return (typ == "copper" and side in {"top", "bottom", "inner"}) or typ in {"mechanical", "drill"}
        self.set_layer_visibility_by_predicate(keep, "Both Copper: top/bottom/inner copper + Edge/Profile + drills only.")

    def silk_only_view(self):
        """Show silkscreen/legend layers plus outline/drills."""
        def keep(layer: Layer) -> bool:
            typ = self.layer_type_from_info(layer)
            return typ in {"silk", "mechanical", "drill"}
        self.set_layer_visibility_by_predicate(keep, "Silks Only: legend/silkscreen + outline + drills.")

    def mask_only_view(self):
        """Show solder mask layers plus outline/drills."""
        def keep(layer: Layer) -> bool:
            typ = self.layer_type_from_info(layer)
            return typ in {"mask", "mechanical", "drill"}
        self.set_layer_visibility_by_predicate(keep, "Mask Only: solder mask + outline + drills.")

    def paste_only_view(self):
        """Show solder paste/stencil layers plus outline/drills."""
        def keep(layer: Layer) -> bool:
            typ = self.layer_type_from_info(layer)
            return typ in {"paste", "mechanical", "drill"}
        self.set_layer_visibility_by_predicate(keep, "Paste Only: paste/stencil + outline + drills.")

    def drill_outline_view(self):
        """Show only board outline/profile and drill files/maps."""
        def keep(layer: Layer) -> bool:
            typ = self.layer_type_from_info(layer)
            return typ in {"mechanical", "drill", "drillmap"}
        self.set_layer_visibility_by_predicate(keep, "Drill / Outline: Edge/Profile + PTH/NPTH/drill layers only.")

    def clean_view(self):
        """KiCad GerbView clean fabrication view.

        This follows GerbView's layer manager idea: keep every file loaded, but
        do not force soldermask/paste over the copper in the main inspection view.
        """
        def keep(layer: Layer) -> bool:
            typ = self.layer_type_from_info(layer)
            side = self.layer_side(layer)
            if typ in {"mechanical", "drill"}:
                return True
            if typ == "silk" and side in {"top", "bottom"}:
                return True
            if typ == "copper" and side == "top":
                return True
            return False
        self.set_layer_visibility_by_predicate(keep, "KiCad GerbView clean: top copper + silks + Edge_Cuts + drills. Mask/Paste/other side hidden, not deleted.")

    def resizeEvent(self, e):
        super().resizeEvent(e)
        # Rebuild only the cached TOP/BOTTOM textures so a larger window gets
        # higher-resolution artwork.  Camera/geometry cache remains intact.
        self._texture_cache_key = None
        self._texture_cache = {}
        self.update()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_F:
            self.canvas.fit()
        elif e.key() == Qt.Key.Key_C:
            self.canvas.center_image()
        elif e.key() == Qt.Key.Key_M:
            self.canvas.toggle_measure()
        elif e.key() == Qt.Key.Key_S:
            self.solo_selected_layer()
        elif e.key() == Qt.Key.Key_A:
            self.set_all(True)
        elif e.key() == Qt.Key.Key_Escape:
            self.canvas.measure_mode = False
            self.canvas.clear_measure()
            self.canvas.clear_highlight()
        elif e.key() == Qt.Key.Key_Delete:
            self.clear_all()


_ORIG_GP_PARSE_EXT = GerberParser.parse_ext
_ORIG_LP_PARSE_EXT = LegacyAltiumGerberParser.parse_ext
_ORIG_GP_EMIT = GerberParser.emit
_ORIG_LP_EMIT = LegacyAltiumGerberParser.emit
_ORIG_GP_PARSE_FILE = GerberParser.parse_file
_ORIG_LP_PARSE_FILE = LegacyAltiumGerberParser.parse_file


def _ugv_reset_universal_state(self):
    self.step_repeat = (1, 1, 0.0, 0.0)  # X count, Y count, I step, J step in mm
    self.quadrant_mode = "multi"          # G75 default in most RS-274X output
    self.zero_omission = "L"              # FS L/T, kept for diagnostics
    self.notation = "absolute"            # FS A/I, kept for diagnostics
    self.attr_file_function = ""
    self.attr_file_polarity = ""


def _ugv_parse_file_gp(self, path: str):
    _ugv_reset_universal_state(self)
    return _ORIG_GP_PARSE_FILE(self, path)


def _ugv_parse_file_lp(self, path: str):
    _ugv_reset_universal_state(self)
    return _ORIG_LP_PARSE_FILE(self, path)


def _ugv_emit_with_step_repeat(self, prim: Primitive):
    """Apply RS-274X SR step-repeat at primitive emission time.

    %SRXnYmIiJj*% repeats every following object.  KiCad/Altium rarely use SR
    now, but older panelized CAM files still do.  Doing the duplication here is
    fast enough and avoids touching the renderer.
    """
    sr = getattr(self, "step_repeat", (1, 1, 0.0, 0.0))
    nx, ny, dx, dy = sr
    try:
        nx, ny = max(1, int(nx)), max(1, int(ny))
        dx, dy = float(dx), float(dy)
    except Exception:
        nx, ny, dx, dy = 1, 1, 0.0, 0.0

    def clone_shift(p: Primitive, ox: float, oy: float) -> Primitive:
        q = Primitive(p.kind)
        q.points = [QPointF(pt.x() + ox, pt.y() + oy) for pt in getattr(p, 'points', [])]
        q.width = p.width
        q.rect = p.rect
        q.radius = p.radius
        if p.contours:
            q.contours = [[QPointF(pt.x() + ox, pt.y() + oy) for pt in contour] for contour in p.contours]
        for k, v in getattr(p, '__dict__', {}).items():
            if k not in {'points', 'contours', 'kind', 'width', 'rect', 'radius'}:
                setattr(q, k, v)
        return q

    orig_emit = _ORIG_LP_EMIT if isinstance(self, LegacyAltiumGerberParser) else _ORIG_GP_EMIT
    if nx == 1 and ny == 1:
        orig_emit(self, prim)
        return
    for ix in range(nx):
        for iy in range(ny):
            orig_emit(self, clone_shift(prim, ix * dx, iy * dy))


def _ugv_parse_ext_common(self, body: str, original):
    b = body.strip()
    bu = b.upper()

    if bu.startswith('TF.FILEFUNCTION'):
        try:
            self.attr_file_function = b.split(',', 1)[1].strip()
        except Exception:
            self.attr_file_function = b
        return
    if bu.startswith('TF.FILEPOLARITY'):
        try:
            self.attr_file_polarity = b.split(',', 1)[1].strip().lower()
        except Exception:
            self.attr_file_polarity = b.lower()
        return

    if bu.startswith('SR'):
        if bu in {'SR', 'SR*'}:
            self.step_repeat = (1, 1, 0.0, 0.0)
            return
        mx = re.search(r'X([0-9]+)', bu)
        my = re.search(r'Y([0-9]+)', bu)
        mi = re.search(r'I([+\-]?(?:\d+(?:\.\d*)?|\.\d+))', bu)
        mj = re.search(r'J([+\-]?(?:\d+(?:\.\d*)?|\.\d+))', bu)
        def cv(m, axis):
            if not m:
                return 0.0
            val = float(m.group(1)) if '.' in m.group(1) else self.coord(m.group(1), axis)
            return val * MM_PER_INCH if ('.' in m.group(1) and self.unit == 'inch') else val
        self.step_repeat = (
            int(mx.group(1)) if mx else 1,
            int(my.group(1)) if my else 1,
            cv(mi, 'X'),
            cv(mj, 'Y'),
        )
        return

    fs = re.search(r'FS([LT])?([AI])?X(\d)(\d)Y(\d)(\d)', bu)
    if fs:
        self.zero_omission = fs.group(1) or 'L'
        self.notation = 'incremental' if (fs.group(2) == 'I') else 'absolute'
        self.abs_mode = self.notation != 'incremental'
        self.x_int, self.x_dec, self.y_int, self.y_dec = map(int, fs.groups()[2:])
        return

    if bu.startswith('IPPOS'):
        self.image_polarity = 'positive'
        return
    if bu.startswith('IPNEG'):
        self.image_polarity = 'negative'
        return

    return original(self, body)


def _ugv_parse_ext_gp(self, body: str):
    return _ugv_parse_ext_common(self, body, _ORIG_GP_PARSE_EXT)


def _ugv_parse_ext_lp(self, body: str):
    return _ugv_parse_ext_common(self, body, _ORIG_LP_PARSE_EXT)


def _ugv_parse_cmd_common(self, cmd: str, original):
    cu = (cmd or '').upper()
    if 'G74' in cu:
        self.quadrant_mode = 'single'
    if 'G75' in cu:
        self.quadrant_mode = 'multi'
    return original(self, cmd)

_ORIG_GP_PARSE_CMD = GerberParser.parse_cmd
_ORIG_LP_PARSE_CMD = LegacyAltiumGerberParser.parse_cmd

def _ugv_parse_cmd_gp(self, cmd: str):
    return _ugv_parse_cmd_common(self, cmd, _ORIG_GP_PARSE_CMD)


def _ugv_parse_cmd_lp(self, cmd: str):
    return _ugv_parse_cmd_common(self, cmd, _ORIG_LP_PARSE_CMD)


def _ugv_eval_macro_expr(expr: str, params: List[float], vars_: Dict[int, float]) -> float:
    """Safe RS-274X aperture macro expression evaluator.

    Supports $variables, + - x/* division and parentheses.  Macro variable
    assignments such as $4=$1/2 are resolved sequentially by _ugv_flash_macro.
    """
    e = expr.strip()
    if not e:
        return 0.0
    e = e.replace('X', '*').replace('x', '*')
    def repl(m):
        idx = int(m.group(1))
        if idx in vars_:
            return str(float(vars_[idx]))
        pi = idx - 1
        return str(float(params[pi]) if 0 <= pi < len(params) else 0.0)
    e = re.sub(r'\$(\d+)', repl, e)
    if not re.fullmatch(r'[0-9eE+\-*/(). ]+', e):
        raise ValueError('unsafe macro expression')
    return float(eval(e, {'__builtins__': {}}, {}))


def _ugv_macro_values(line: str, params: List[float], vars_: Dict[int, float]) -> Optional[List[float]]:
    vals = []
    for token in line.split(','):
        token = token.strip()
        if not token:
            continue
        vals.append(_ugv_eval_macro_expr(token, params, vars_))
    return vals if vals else None


def _ugv_emit_macro_primitive(parser, obj: Primitive, exposure: int, old_pol: str):
    macro_pol = 'clear' if int(exposure) == 0 else old_pol
    obj.polarity = macro_pol
    try:
        obj.aperture_code = str(parser.current_ap)
    except Exception:
        pass
    parser.emit(obj)


def _ugv_flash_macro(self, ap: Aperture, x: float, y: float) -> bool:
    macro = self.aperture_macros.get(ap.kind.upper())
    hint = self.aperture_param_hints.get(ap.code, {})

    if not macro and hint:
        sx = float(hint.get('x', 0.0) or 0.0)
        sy = float(hint.get('y', 0.0) or 0.0)
        rot = float(hint.get('rot', 0.0) or 0.0)
        if sx > 0 and sy > 0:
            self.emit(self.polygon_rect(x, y, sx, sy, rot))
            return True
        return False
    if not macro:
        return False

    vars_: Dict[int, float] = {}
    emitted = False
    old_pol = self.polarity

    for raw in macro.split('*'):
        line = raw.strip()
        if not line or line.startswith('0'):
            continue
        am = re.match(r'\$(\d+)=(.+)$', line)
        if am:
            try:
                vars_[int(am.group(1))] = _ugv_eval_macro_expr(am.group(2), ap.params, vars_)
            except Exception:
                pass
            continue
        try:
            vals = _ugv_macro_values(line, ap.params, vars_)
        except Exception:
            continue
        if not vals:
            continue
        prim = int(vals[0])
        exposure = int(vals[1]) if len(vals) > 1 else 1

        try:
            if prim == 1 and len(vals) >= 5:
                d, cx, cy = vals[2], vals[3], vals[4]
                rot = vals[5] if len(vals) > 5 else 0.0
                rx, ry = self.rotate_point(cx, cy, rot)
                _ugv_emit_macro_primitive(self, Primitive('circle', points=[QPointF(x + rx, y + ry)], radius=abs(d) / 2.0), exposure, old_pol)
                emitted = True

            elif prim == 20 and len(vals) >= 7:
                w, x1, y1, x2, y2 = vals[2], vals[3], vals[4], vals[5], vals[6]
                rot = vals[7] if len(vals) > 7 else 0.0
                rx1, ry1 = self.rotate_point(x1, y1, rot)
                rx2, ry2 = self.rotate_point(x2, y2, rot)
                _ugv_emit_macro_primitive(self, Primitive('line', points=[QPointF(x + rx1, y + ry1), QPointF(x + rx2, y + ry2)], width=abs(w)), exposure, old_pol)
                emitted = True

            elif prim == 21 and len(vals) >= 7:
                w, h, cx, cy, rot = vals[2], vals[3], vals[4], vals[5], vals[6]
                rcx, rcy = self.rotate_point(cx, cy, rot)
                _ugv_emit_macro_primitive(self, self.polygon_rect(x + rcx, y + rcy, abs(w), abs(h), rot), exposure, old_pol)
                emitted = True

            elif prim == 22 and len(vals) >= 7:
                w, h, xll, yll = vals[2], vals[3], vals[4], vals[5]
                rot = vals[6] if len(vals) > 6 else 0.0
                cx, cy = xll + w / 2.0, yll + h / 2.0
                rcx, rcy = self.rotate_point(cx, cy, rot)
                _ugv_emit_macro_primitive(self, self.polygon_rect(x + rcx, y + rcy, abs(w), abs(h), rot), exposure, old_pol)
                emitted = True

            elif prim == 4 and len(vals) >= 5:
                n = max(1, int(vals[2]))
                coord_end = 3 + (n + 1) * 2
                coords = vals[3:coord_end]
                rot = vals[coord_end] if len(vals) > coord_end else 0.0
                pts = []
                for i in range(0, len(coords) - 1, 2):
                    rx, ry = self.rotate_point(coords[i], coords[i + 1], rot)
                    pts.append(QPointF(x + rx, y + ry))
                if len(pts) >= 2 and abs(pts[0].x() - pts[-1].x()) < 1e-9 and abs(pts[0].y() - pts[-1].y()) < 1e-9:
                    pts.pop()
                if len(pts) >= 3:
                    _ugv_emit_macro_primitive(self, Primitive('polygon', points=pts), exposure, old_pol)
                    emitted = True

            elif prim == 5 and len(vals) >= 6:
                n = max(3, int(vals[2]))
                cx, cy, d = vals[3], vals[4], vals[5]
                rot = vals[6] if len(vals) > 6 else 0.0
                pts = []
                for a in range(n):
                    px = (d / 2.0) * math.cos(math.radians(rot) + 2 * math.pi * a / n)
                    py = (d / 2.0) * math.sin(math.radians(rot) + 2 * math.pi * a / n)
                    pts.append(QPointF(x + cx + px, y + cy + py))
                _ugv_emit_macro_primitive(self, Primitive('polygon', points=pts), exposure, old_pol)
                emitted = True

            elif prim == 6 and len(vals) >= 8:
                cx, cy, od, ring_t, gap, rings, cross_t, cross_len = vals[2], vals[3], vals[4], vals[5], vals[6], int(vals[7]), vals[8] if len(vals)>8 else 0.0, vals[9] if len(vals)>9 else 0.0
                rr = max(od / 2.0, 0.0)
                for k in range(max(1, rings)):
                    r = rr - k * (abs(ring_t) + abs(gap))
                    if r <= 0: break
                    _ugv_emit_macro_primitive(self, Primitive('circle', points=[QPointF(x + cx, y + cy)], radius=r), exposure, old_pol)
                if cross_t > 0 and cross_len > 0:
                    _ugv_emit_macro_primitive(self, Primitive('line', points=[QPointF(x + cx - cross_len/2, y + cy), QPointF(x + cx + cross_len/2, y + cy)], width=cross_t), exposure, old_pol)
                    _ugv_emit_macro_primitive(self, Primitive('line', points=[QPointF(x + cx, y + cy - cross_len/2), QPointF(x + cx, y + cy + cross_len/2)], width=cross_t), exposure, old_pol)
                emitted = True

            elif prim == 7 and len(vals) >= 7:
                if len(vals) >= 8:
                    cx, cy, od, inner, gap, rot = vals[2], vals[3], vals[4], vals[5], vals[6], vals[7]
                else:  # old Altium/CAMtastic shortened variant seen in the user's files
                    cx, cy, od, inner, gap, rot = vals[2], 0.0, vals[3], vals[4], vals[5], vals[6]
                rcx, rcy = self.rotate_point(cx, cy, rot)
                thermal = Primitive('thermal', points=[QPointF(x + rcx, y + rcy)], radius=abs(od) / 2.0)
                thermal.outer_d = abs(od)
                thermal.inner_d = abs(inner)
                thermal.gap = abs(gap)
                thermal.rotation = float(rot)
                _ugv_emit_macro_primitive(self, thermal, 1, old_pol)
                emitted = True
        finally:
            self.polarity = old_pol

    return emitted


GerberParser.parse_file = _ugv_parse_file_gp
LegacyAltiumGerberParser.parse_file = _ugv_parse_file_lp
GerberParser.emit = _ugv_emit_with_step_repeat
LegacyAltiumGerberParser.emit = _ugv_emit_with_step_repeat
GerberParser.parse_ext = _ugv_parse_ext_gp
LegacyAltiumGerberParser.parse_ext = _ugv_parse_ext_lp
GerberParser.parse_cmd = _ugv_parse_cmd_gp
LegacyAltiumGerberParser.parse_cmd = _ugv_parse_cmd_lp
GerberParser.flash_macro = _ugv_flash_macro
LegacyAltiumGerberParser.flash_macro = _ugv_flash_macro

_ORIG_EX_PARSE_LINES = ExcellonParser._parse_lines
_ORIG_EX_NUM = ExcellonParser.num

def _ugv_ex_parse_lines(self, lines: List[str]) -> List[Primitive]:
    self.zero_suppression = getattr(self, 'zero_suppression', 'LZ')
    for raw in lines:
        line = raw.strip().upper().replace(' ', '')
        fmt = re.search(r'(?:FILE_FORMAT|FORMAT)\s*=\s*(\d+)\s*[:.]\s*(\d+)', line)
        if fmt:
            self.decimals = int(fmt.group(2)); self.format_locked = True
        if 'METRIC' in line or 'M71' in line:
            self.unit = 'mm'
            if not self.format_locked: self.decimals = 3
        if 'INCH' in line or 'M72' in line:
            self.unit = 'inch'
            if not self.format_locked: self.decimals = 4
        if ',TZ' in line or 'TZ' == line:
            self.zero_suppression = 'TZ'
        if ',LZ' in line or 'LZ' == line:
            self.zero_suppression = 'LZ'
    return _ORIG_EX_PARSE_LINES(self, lines)

def _ugv_ex_num(self, s: str) -> float:
    if '.' in s:
        v = float(s)
    else:
        sign = -1 if s.startswith('-') else 1
        body = s.lstrip('+-') or '0'
        total = (2 if self.unit == 'inch' else 3) + int(self.decimals)
        if getattr(self, 'zero_suppression', 'LZ') == 'TZ' and len(body) < total:
            body = body + ('0' * (total - len(body)))
        v = sign * int(body) / (10 ** int(self.decimals))
    return v * MM_PER_INCH if self.unit == 'inch' else v

ExcellonParser._parse_lines = _ugv_ex_parse_lines
ExcellonParser.num = _ugv_ex_num

_ORIG_MAIN_READ_FILE_FUNCTION = MainWindow.read_gerber_file_function

def _ugv_read_gerber_file_function(path: str) -> str:
    try:
        ff = _ORIG_MAIN_READ_FILE_FUNCTION(path)
    except TypeError:
        ff = _ORIG_MAIN_READ_FILE_FUNCTION.__func__(path) if hasattr(_ORIG_MAIN_READ_FILE_FUNCTION, '__func__') else ''
    if ff:
        return ff
    try:
        text = Path(path).read_text(errors='ignore')[:200000]
        m = re.search(r'%TF\.FileFunction,([^*%]+)\*%', text, re.I)
        return m.group(1).strip() if m else ''
    except Exception:
        return ''

MainWindow.read_gerber_file_function = staticmethod(_ugv_read_gerber_file_function)



# ---------------------------------------------------------------------------
# v2.22 ALL-CAD / LEGACY + MODERN LAYER CLASSIFIER PATCH
# Added after the clean core so the UI/style/fast renderer remain untouched.
# The classifier below intentionally scores metadata, filename and extension
# together; .ART/.PHO/.GBR/.GER cannot be trusted by extension alone.
# ---------------------------------------------------------------------------

# Extra legacy CAM extensions seen in older Ultiboard/Multisim, PADS, CADSTAR,
# Zuken, Target/Sprint/DesignSpark/fab-house packages. They are renderable only
# when their content is Gerber-like; reports are still filtered by classifier.
GERBER_EXTS.update({
    '.tsk', '.bsk', '.tsm', '.bsm', '.tsp', '.bsp', '.ssl', '.bsl',
    '.mgt', '.mgb', '.cmp', '.ly2', '.ly3', '.ly4', '.ly5', '.ly6',
    '.ncl', '.ncr', '.rou', '.route', '.profile', '.outline', '.mech',
    '.asm', '.assy', '.drd', '.map'
})
DRILL_EXTS.update({'.dri', '.drd', '.rl', '.rou', '.ncl', '.ncr'})
CAM_OPEN_EXTS.update(GERBER_EXTS | DRILL_EXTS | {'.txt'})

_UGV_HELPER_ROLES = {'mechanical', 'profile', 'drill', 'drillmap'}
_UGV_ROLE_ALIASES = {
    'copper': (
        'copper','cu','signal','sig','layer','artwork','conductor','track','tracks','trace','foil',
        'toplayer','bottomlayer','top_layer','bottom_layer','l1','l2','l3','l4','primary','secondary'
    ),
    'mask': (
        'soldermask','solder_mask','solderresist','solder_resist','resist','mask','stop','stopmask',
        'stop_mask','solder_stop','tstop','bstop','sm_top','sm_bottom','smtop','smbot','smt','smb','tsm','bsm',
        'mt_pho','mb_pho'
    ),
    'paste': (
        'paste','solderpaste','solder_paste','cream','paste_mask','pastemask','stencil','tcream','bcream',
        'tsp','bsp','spt','spb','pt_pho','pb_pho'
    ),
    'silk': (
        'silk','silkscreen','silk_screen','legend','overlay','ident','nomenclature','componentprint',
        'component_print','placement','tplace','bplace','tsilk','bsilk','sst','ssb','tsk','bsk','st_pho','sb_pho'
    ),
    'assembly': ('assembly','assy','fabdrawing','fab_drawing','fabrication','fabrication_drawing','drawing','readme'),
    'mechanical': (
        'profile','edge','edges','edge_cuts','edgecuts','boardoutline','board_outline','outline','dimension',
        'dim','route','routing','rout','milling','mill','mechanical','mech','keepout','keep_out','contour',
        'border','cutout','cut_out','gko','gml','gm1','gm2','oln'
    ),
    'drillmap': ('drilldrawing','drill_drawing','drillmap','drill_map','drillguide','drill_guide','holechart','hole_chart'),
    'pads': ('padmaster','pad_master','pads_master','pad_master_top','pad_master_bottom'),
}

_UGV_TOP_ALIASES = (
    'top','front','component','component_side','componentlayer','component_layer','comp','primary','upper',
    'f_cu','f_mask','f_paste','f_silk','f_silkscreen','f_silks','topside','top_side','toplayer','top_layer',
    'copper_top','top_copper','soldermask_top','topsoldermask','top_soldermask','top_solder_mask',
    'silkscreen_top','topsilkscreen','top_silkscreen','top_silk','paste_top','top_paste','toppaste',
    'topoverlay','top_overlay','top_resist','top_stop','tstop','tcream','tplace','tsilk','smt','sst','spt',
    'gtl','gts','gtp','gto','gpt','cmp','plc','stc','crc','l1','layer1','layer_1','l1_pho','mt_pho','pt_pho','st_pho'
)
_UGV_BOTTOM_ALIASES = (
    'bottom','bot','back','solder','solder_side','solderlayer','solder_layer','secondary','lower',
    'b_cu','b_mask','b_paste','b_silk','b_silkscreen','b_silks','bottomside','bottom_side','bottomlayer','bottom_layer',
    'copper_bottom','bottom_copper','soldermask_bottom','bottomsoldermask','bottom_soldermask','bottom_solder_mask',
    'silkscreen_bottom','bottomsilkscreen','bottom_silkscreen','bottom_silk','paste_bottom','bottom_paste','bottompaste',
    'bottomoverlay','bottom_overlay','bottom_resist','bottom_stop','bstop','bcream','bplace','bsilk','smb','ssb','spb',
    'gbl','gbs','gbp','gbo','gpb','sol','pls','sts','crs','bot','mb_pho','pb_pho','sb_pho'
)
_UGV_INNER_ALIASES = (
    'inner','internal','internalplane','internal_plane','plane','midlayer','mid_layer','power','gnd','ground','vcc',
    'in1','in2','in3','in4','inner1','inner2','inner3','inner4','layer2','layer3','layer4','l2','l3','l4','l5','l6',
    'g1','g2','g3','g4','gp1','gp2','gp3','gp4','ly2','ly3','ly4','ly5','ly6'
)

_UGV_EXT_SIDE = {
    '.gtl':'top','.gts':'top','.gtp':'top','.gto':'top','.gpt':'top','.top':'top','.cmp':'top',
    '.plc':'top','.stc':'top','.crc':'top','.smt':'top','.sst':'top','.spt':'top','.tsk':'top','.tsm':'top','.tsp':'top','.l1':'top',
    '.gbl':'bottom','.gbs':'bottom','.gbp':'bottom','.gbo':'bottom','.gpb':'bottom','.bot':'bottom','.sol':'bottom',
    '.pls':'bottom','.sts':'bottom','.crs':'bottom','.smb':'bottom','.ssb':'bottom','.spb':'bottom','.bsk':'bottom','.bsm':'bottom','.bsp':'bottom',
}
_UGV_EXT_ROLE = {
    '.gtl':'copper','.gbl':'copper','.cmp':'copper','.sol':'copper','.top':'copper','.bot':'copper',
    '.g1':'copper','.g2':'copper','.g3':'copper','.g4':'copper','.g5':'copper','.g6':'copper',
    '.l1':'copper','.l2':'copper','.l3':'copper','.l4':'copper','.l5':'copper','.l6':'copper',
    '.ly2':'copper','.ly3':'copper','.ly4':'copper','.gp1':'copper','.gp2':'copper','.gp3':'copper','.gp4':'copper',
    '.gts':'mask','.gbs':'mask','.smt':'mask','.smb':'mask','.stc':'mask','.sts':'mask','.tsm':'mask','.bsm':'mask',
    '.gtp':'paste','.gbp':'paste','.spt':'paste','.spb':'paste','.crc':'paste','.crs':'paste','.tsp':'paste','.bsp':'paste',
    '.gto':'silk','.gbo':'silk','.sst':'silk','.ssb':'silk','.plc':'silk','.pls':'silk','.tsk':'silk','.bsk':'silk',
    '.gpt':'pads','.gpb':'pads',
    '.gko':'mechanical','.gm1':'mechanical','.gm2':'mechanical','.gm3':'mechanical','.gm4':'mechanical','.gml':'mechanical',
    '.oln':'mechanical','.dim':'mechanical','.out':'mechanical','.fab':'assembly','.asm':'assembly','.assy':'assembly',
}


def _ugv_norm_token_text(path_or_text: str) -> str:
    raw = Path(str(path_or_text)).name.lower()
    # Preserve extension as a token pair too: L1.PHO -> l1_pho, board.GTL -> board_gtl
    return re.sub(r'[^a-z0-9]+', '_', raw).strip('_')


def _ugv_has_token(n: str, token: str) -> bool:
    token = token.strip('_').lower()
    if not token:
        return False
    if '_' in token:
        return token in n
    return re.search(r'(^|_)' + re.escape(token) + r'(_|$)', n) is not None


def _ugv_text_role_score(text: str) -> dict:
    n = _ugv_norm_token_text(text)
    score = {k: 0 for k in ('copper','mask','paste','silk','assembly','mechanical','drillmap','pads')}
    for role, toks in _UGV_ROLE_ALIASES.items():
        for tok in toks:
            if _ugv_has_token(n, tok) or tok in n:
                score[role] += 30 if '_' in tok or len(tok) > 3 else 14
    # negative priority: avoid classifying mask/silk/paste as copper just because filename contains layer/top/bottom
    if any(score[r] > 0 for r in ('mask','paste','silk','assembly','mechanical','drillmap','pads')):
        score['copper'] -= 20
    return score


def _ugv_text_side_score(text: str) -> dict:
    n = _ugv_norm_token_text(text)
    score = {'top': 0, 'bottom': 0, 'inner': 0, 'both': 0, 'unknown': 0}
    for tok in _UGV_TOP_ALIASES:
        if _ugv_has_token(n, tok) or tok in n:
            score['top'] += 22 if len(tok) > 3 else 10
    for tok in _UGV_BOTTOM_ALIASES:
        if _ugv_has_token(n, tok) or tok in n:
            score['bottom'] += 22 if len(tok) > 3 else 10
    for tok in _UGV_INNER_ALIASES:
        if _ugv_has_token(n, tok) or tok in n:
            score['inner'] += 18
    if any(tok in n for tok in ('outline','board_outline','edge_cuts','edgecuts','profile','mechanical','dimension','drill','holes','pth','npth')):
        score['both'] += 60
    return score


def _ugv_read_head(path: str, limit: int = 220000) -> str:
    try:
        return Path(path).read_text(errors='ignore')[:limit]
    except Exception:
        return ''


def _ugv_extrep_desc(path: str) -> str:
    try:
        return MainWindow.read_altium_extrep_description(path) or ''
    except Exception:
        return ''


def _ugv_detect_cad_family(path: str) -> str:
    n = _ugv_norm_token_text(path)
    ext = Path(path).suffix.lower()
    attrs = {}
    try:
        attrs = MainWindow.read_gerber_attributes(path) or {}
    except Exception:
        pass
    gen = (attrs.get('generationsoftware','') or '').lower()
    head = _ugv_read_head(path, 80000).lower()
    blob = ' '.join((n, gen, head[:5000]))
    if 'kicad' in blob or any(x in n for x in ('f_cu','b_cu','edge_cuts','f_mask','b_mask','f_paste','b_paste')):
        return 'kicad'
    if 'easyeda' in blob or n.startswith('gerber_') or any(x in n for x in ('topsoldermasklayer','bottomsoldermasklayer','topsilklayer','boardoutlinelayer')):
        return 'easyeda'
    if any(x in blob for x in ('ultiboard','multisim','national instruments','electronics workbench','ewb')) or any(x in n for x in ('toplayer','bottomlayer','topsoldermask','bottomsoldermask','topsilkscreen','bottomsilkscreen')) and ext in {'.ger','.gbr','.art'}:
        return 'ni-ultiboard/multisim'
    if any(x in blob for x in ('proteus','ares')) or any(x in n for x in ('proteus','ares','top_resist','bottom_resist','cadcam')):
        return 'proteus/ares'
    if any(x in blob for x in ('altium','protel','camtastic')) or any(x in n for x in ('topoverlay','bottomoverlay','internalplane','midlayer','mechanical')):
        return 'altium/protel/camtastic'
    if 'eagle' in blob or ext in {'.cmp','.sol','.plc','.pls','.stc','.sts','.crc','.crs'} or any(x in n for x in ('tcream','bcream','tstop','bstop','tplace','bplace')):
        return 'eagle'
    if 'diptrace' in blob or any(x in n for x in ('topmask','bottommask','topsilk','bottomsilk','boardoutline')):
        return 'diptrace'
    if any(x in blob for x in ('pads','powerpcb','mentor graphics','xpedition')) or any(x in n for x in ('l1_pho','l2_pho','st_pho','mt_pho','pt_pho','smt','smb','sst','ssb','spt','spb')):
        return 'mentor-pads/xpedition'
    if any(x in blob for x in ('orcad','allegro','cadence')) or (ext == '.art' and any(x in n for x in ('top','bottom','etch','silk','mask','paste'))):
        return 'orcad/allegro'
    if any(x in blob for x in ('zuken','cadstar')) or any(x in n for x in ('cadstar','zuken','cr5000','cr8000')):
        return 'zuken/cadstar'
    if any(x in blob for x in ('designspark','target 3001','target3001','sprint-layout','sprint layout','circuitmaker','circuitstudio','fusion 360')):
        return 'other-cad'
    if attrs.get('filefunction',''):
        return 'x2-gerber'
    return 'generic'


def _ugv_role_from_x2(ff: str) -> str:
    f = (ff or '').replace(' ', '').replace('_','').lower()
    if not f:
        return ''
    if 'copper' in f: return 'copper'
    if 'soldermask' in f or 'mask' in f: return 'mask'
    if 'paste' in f: return 'paste'
    if 'legend' in f or 'silkscreen' in f or 'silk' in f: return 'silk'
    if 'profile' in f or 'rout' in f or 'edge' in f or 'outline' in f: return 'mechanical'
    if 'drill' in f: return 'drill'
    return ''


def _ugv_side_from_x2(ff: str) -> str:
    f = (ff or '').replace(' ', '').lower()
    if not f:
        return ''
    if ',top' in f or f.endswith('top') or 'copper,l1' in f:
        return 'top'
    if ',bot' in f or ',bottom' in f or f.endswith('bot') or f.endswith('bottom'):
        return 'bottom'
    if re.search(r'copper,l[2-9]', f) and not any(x in f for x in (',top',',bot',',bottom')):
        return 'inner'
    if any(x in f for x in ('profile','rout','drill','npth','pth','nonplated','plated')):
        return 'both'
    return ''


def _ugv_classify_layer_type(self, path: str) -> str:
    raw = Path(path).name.lower()
    ext = Path(path).suffix.lower()
    n = _ugv_norm_token_text(path)
    if ext in CAM_METADATA_EXTS or ext in {'.drr','.log','.lst','.rpt','.pdf','.png','.jpg','.csv'}:
        return 'ignore'
    if any(k in n for k in ('status_report','transcode_report','readme','read_me','gerber_job','job_file','ncdrill_report')) and ext in {'.txt','.rep','.gbrjob'}:
        return 'ignore'
    try:
        if self.is_drill(path):
            return 'drill'
    except Exception:
        pass
    ff = ''
    try: ff = self.read_gerber_file_function(path)
    except Exception: pass
    role = _ugv_role_from_x2(ff)
    if role:
        return role
    desc = _ugv_extrep_desc(path)
    scores = {k: 0 for k in ('copper','mask','paste','silk','assembly','mechanical','drillmap','pads')}
    # sidecar descriptions from Altium/CAMtastic are stronger than filename
    for k, v in _ugv_text_role_score(desc).items(): scores[k] += v * 3
    for k, v in _ugv_text_role_score(raw).items(): scores[k] += v
    if ext in _UGV_EXT_ROLE:
        scores[_UGV_EXT_ROLE[ext]] += 85
    # .ART/.PHO/.GBR/.GER are deliberately ambiguous; use content/title comments only as weak help.
    head = _ugv_read_head(path, 12000)
    for k, v in _ugv_text_role_score(head[:2000]).items(): scores[k] += int(v * 0.4)
    # Common PADS/OrCAD/Ultiboard filename forms: L1.PHO, MT.PHO, TOP.ART, Bottom Layer.ger
    if re.search(r'(^|_)l1(_|$).*(_|\.)pho$', n): scores['copper'] += 80
    if re.search(r'(^|_)l[2-9](_|$).*(_|\.)pho$', n): scores['copper'] += 70
    if re.search(r'(^|_)(st|sb)(_)?pho$', n): scores['silk'] += 80
    if re.search(r'(^|_)(mt|mb)(_)?pho$', n): scores['mask'] += 80
    if re.search(r'(^|_)(pt|pb)(_)?pho$', n): scores['paste'] += 80
    # If only side is known on a generic artwork file, copper is the safest fabrication role.
    side_scores = _ugv_text_side_score(raw)
    if ext in {'.gbr','.ger','.pho','.art','.gbx'} and max(side_scores.values()) >= 20 and max(scores.values()) <= 0:
        scores['copper'] += 25
    best = max(scores, key=scores.get)
    return best if scores[best] > 0 else 'generic'


def _ugv_layer_side_name(name: str) -> str:
    raw = Path(str(name)).name.lower()
    ext = Path(raw).suffix.lower()
    n = _ugv_norm_token_text(raw)
    if ext in _UGV_EXT_SIDE:
        return _UGV_EXT_SIDE[ext]
    if ext in {'.gko','.gm1','.gm2','.gm3','.gm4','.gml','.oln','.dim','.out','.fab','.drd','.map'}:
        return 'both'
    if ext in {'.g2','.g3','.g4','.g5','.g6','.gp1','.gp2','.gp3','.gp4','.l2','.l3','.l4','.l5','.l6','.ly2','.ly3','.ly4','.ly5','.ly6'}:
        return 'inner'
    score = _ugv_text_side_score(raw)
    # Exact KiCad forms
    if re.search(r'(^|_)f_(cu|mask|paste|silk|silkscreen|silks)(_|$)', n): score['top'] += 100
    if re.search(r'(^|_)b_(cu|mask|paste|silk|silkscreen|silks)(_|$)', n): score['bottom'] += 100
    if re.search(r'(^|_)in\d+_cu(_|$)', n): score['inner'] += 100
    best = max(score, key=score.get)
    if score[best] <= 0:
        return 'unknown'
    # if helper tokens dominate, treat as shared outline/drill
    if score['both'] >= max(score['top'], score['bottom'], score['inner']):
        return 'both'
    return best


def _ugv_layer_side_from_file(self, path: str) -> str:
    ff = ''
    try: ff = self.read_gerber_file_function(path)
    except Exception: pass
    sx = _ugv_side_from_x2(ff)
    if sx:
        return sx
    desc = _ugv_extrep_desc(path)
    if desc:
        score = _ugv_text_side_score(desc)
        best = max(score, key=score.get)
        if score[best] > 0:
            return best
    return _ugv_layer_side_name(path)


def _ugv_top_view(self):
    def keep(layer: Layer) -> bool:
        side = self.layer_side(layer)
        typ = self.layer_type_from_info(layer)
        if typ in _UGV_HELPER_ROLES and side in {'both','unknown','top'}:
            return True
        return side == 'top' and typ in {'copper','silk','mask','paste','pads'}
    self.set_layer_visibility_by_predicate(keep, 'Top View: TOP copper/mask/paste/silk + shared outline/drills only.')


def _ugv_bottom_view(self):
    def keep(layer: Layer) -> bool:
        side = self.layer_side(layer)
        typ = self.layer_type_from_info(layer)
        if typ in _UGV_HELPER_ROLES and side in {'both','unknown','bottom'}:
            return True
        return side == 'bottom' and typ in {'copper','silk','mask','paste','pads'}
    self.set_layer_visibility_by_predicate(keep, 'Bottom View: BOTTOM copper/mask/paste/silk + shared outline/drills only.')


def _ugv_top_copper_only(self):
    def keep(layer: Layer) -> bool:
        side = self.layer_side(layer)
        typ = self.layer_type_from_info(layer)
        if typ in _UGV_HELPER_ROLES and side in {'both','unknown','top'}:
            return True
        return typ == 'copper' and side == 'top'
    self.set_layer_visibility_by_predicate(keep, 'Top Copper Only: real TOP copper + shared outline/drills. Mask/paste/silk/bottom/inner OFF.')


def _ugv_bottom_copper_only(self):
    def keep(layer: Layer) -> bool:
        side = self.layer_side(layer)
        typ = self.layer_type_from_info(layer)
        if typ in _UGV_HELPER_ROLES and side in {'both','unknown','bottom'}:
            return True
        return typ == 'copper' and side == 'bottom'
    self.set_layer_visibility_by_predicate(keep, 'Bottom Copper Only: real BOTTOM copper + shared outline/drills. Mask/paste/silk/top/inner OFF.')

MainWindow.detect_cad_family = staticmethod(_ugv_detect_cad_family)
MainWindow.classify_layer_type = _ugv_classify_layer_type
MainWindow.layer_side_name = staticmethod(_ugv_layer_side_name)
MainWindow.layer_side_from_file = _ugv_layer_side_from_file
MainWindow.top_view = _ugv_top_view
MainWindow.bottom_view = _ugv_bottom_view
MainWindow.top_copper_only = _ugv_top_copper_only
MainWindow.bottom_copper_only = _ugv_bottom_copper_only



# -----------------------------------------------------------------------------
# ULTRA 3D PCB VIEWER EXTENSION
# Integrated accelerated 3D/isometric PCB renderer using existing parsed Gerber layers.
# Cached camera/bounds, fast interactive mode, no Gerber re-parse.
# -----------------------------------------------------------------------------
from PyQt6.QtWidgets import QDialog, QComboBox, QCheckBox


class PCB3DWidget(QWidget):
    """Lightweight solid 3D PCB preview.

    Fast architecture: build flat TOP/BOTTOM artwork textures once, then rotate
    two opaque board faces during interaction. This matches the practical way a
    quick PCB 3D preview stays smooth: no primitive-by-primitive repaint inside
    the rotation loop, no transparency, fixed 1.5 mm FR4 body, Edge.Cuts-sized.
    """

    def __init__(self, owner: MainWindow, parent=None):
        super().__init__(parent)
        self.owner = owner
        self.mode = "both"
        self.show_board = True
        self.board_thickness_mm = PCB_THICKNESS_MM
        self.rot_x = -58.0
        self.rot_y = 0.0
        self.rot_z = -35.0
        self.angle = self.rot_z
        self.tilt = self.rot_x
        self.zoom = 1.0
        self.pan = QPointF(0, 0)
        self.last_mouse = QPointF()
        self.panning = False
        self.rotating = False
        self.fast_interaction = False
        self._quality_timer = QTimer(self)
        self._quality_timer.setSingleShot(True)
        self._quality_timer.timeout.connect(self._finish_fast_interaction)
        self._bounds_cache_key = None
        self._bounds_cache = QRectF()
        self._body_path_cache_key = None
        self._body_path_cache = None
        self._texture_cache_key = None
        self._texture_cache = {}
        self._paint_center = QPointF(0, 0)
        self.setMinimumSize(1180, 760)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setStyleSheet("background:#070b14;")

    def set_mode(self, mode: str):
        self.mode = mode
        self.update()

    def _finish_fast_interaction(self):
        self.fast_interaction = False
        self.update()

    def _start_fast_interaction(self):
        self.fast_interaction = True
        self._quality_timer.start(90)

    def invalidate_cache(self):
        self._bounds_cache_key = None
        self._bounds_cache = QRectF()
        self._body_path_cache_key = None
        self._body_path_cache = None
        self._texture_cache_key = None
        self._texture_cache = {}
        self.update()

    def _layers_key(self):
        layers = getattr(self.owner, 'layers', []) or []
        return tuple((getattr(l, 'name', ''), len(getattr(l, 'primitives', []) or []), getattr(l, 'visible', True)) for l in layers)

    def board_body_path(self) -> QPainterPath:
        key = self._layers_key()
        if key == self._body_path_cache_key and self._body_path_cache is not None:
            return QPainterPath(self._body_path_cache)
        try:
            layers = getattr(self.owner, 'layers', []) or []
            rr = getattr(self.owner, 'renderer', None)
            if rr is not None and layers:
                ref = rr.export_production_bounds(layers).normalized()
                if not ref.isValid() or ref.width() <= 0 or ref.height() <= 0:
                    ref = rr.bounds(layers).normalized()
                body = rr.safe_realistic_body(layers, ref)
                bb = body.boundingRect().normalized()
                if bb.isValid() and bb.width() > 0 and bb.height() > 0:
                    self._body_path_cache_key = key
                    self._body_path_cache = QPainterPath(body)
                    return QPainterPath(body)
        except Exception:
            pass
        fallback = QPainterPath()
        fallback.setFillRule(Qt.FillRule.OddEvenFill)
        fallback.addRect(QRectF(-50, -30, 100, 60))
        self._body_path_cache_key = key
        self._body_path_cache = QPainterPath(fallback)
        return fallback

    def board_bounds(self) -> QRectF:
        key = self._layers_key()
        if key == self._bounds_cache_key and self._bounds_cache.isValid():
            return QRectF(self._bounds_cache)
        body = self.board_body_path()
        ref = body.boundingRect().normalized()
        if not ref.isValid() or ref.width() <= 0 or ref.height() <= 0:
            ref = QRectF(-50, -30, 100, 60)
        self._bounds_cache_key = key
        self._bounds_cache = QRectF(ref)
        return ref

    def fit(self):
        wb = self.board_bounds()
        if wb.isValid() and wb.width() > 0 and wb.height() > 0:
            sx = self.width() / max(wb.width(), 1.0)
            sy = self.height() / max(wb.height(), 1.0)
            self.zoom = max(1.0, min(sx, sy) * 0.58)
            self.pan = QPointF(0, 0)
        self.update()

    def rotate3d(self, x: float, y: float, z: float) -> tuple[float, float, float]:
        x -= self._paint_center.x()
        y -= self._paint_center.y()
        rz = math.radians(self.rot_z)
        cz, sz = math.cos(rz), math.sin(rz)
        x, y = x * cz - y * sz, x * sz + y * cz
        ry = math.radians(self.rot_y)
        cy, sy = math.cos(ry), math.sin(ry)
        x, z = x * cy + z * sy, -x * sy + z * cy
        rx = math.radians(self.rot_x)
        cx, sx = math.cos(rx), math.sin(rx)
        y, z = y * cx - z * sx, y * sx + z * cx
        return x, y, z

    def project(self, x: float, y: float, z: float) -> QPointF:
        xr, yr, _zr = self.rotate3d(x, y, z)
        return QPointF(self.width() / 2 + self.pan.x() + xr * self.zoom,
                       self.height() / 2 + self.pan.y() - yr * self.zoom)

    def camera_depth(self, x: float, y: float, z: float) -> float:
        return self.rotate3d(x, y, z)[2]

    def layer_allowed_for_side(self, layer: Layer, side_name: str) -> bool:
        typ = self.owner.layer_type_from_info(layer)
        side = self.owner.layer_side(layer)
        # Mechanical/profile layers are not drawn as colored artwork, except
        # documentation/fill layers that some CAD exports classify as mechanical
        # but visually belong to the white bottom/top legend area.
        if typ == 'mechanical':
            lname = (getattr(layer, 'name', '') or '').lower()
            if any(k in lname for k in ('3d', 'body', 'courtyard', 'assembly', 'drawing', 'legend', 'silk')):
                return True
            return False
        if typ == 'drill':
            return True
        if self.mode == 'copper' and typ not in {'copper', 'pads', 'drill'}:
            return False
        if self.mode == 'top' and side_name != 'top':
            return False
        if self.mode == 'bottom' and side_name != 'bottom':
            return False
        if typ not in {'copper', 'mask', 'paste', 'silk', 'pads', 'drill', 'mechanical'}:
            return False
        if side_name == 'top':
            return side in {'top', 'both', 'unknown', 'inner'} or typ == 'drill'
        return side in {'bottom', 'both', 'unknown', 'inner'} or typ == 'drill'

    def color_for_layer(self, layer: Layer) -> QColor:
        typ = self.owner.layer_type_from_info(layer)
        # Palette tuned from the supplied reference PNG:
        # soldermask: saturated PCB green, traces: darker green under mask,
        # exposed copper/pads: warm ENIG gold, silk: clean white, drills: black.
        if typ == 'mask':
            return QColor(44, 168, 22, 255)      # main soldermask green
        if typ == 'mechanical':
            return silk, False
        if typ == 'copper':
            return QColor(20, 105, 22, 255)      # masked tracks / copper under mask
        if typ == 'pads':
            return QColor(255, 185, 31, 255)     # ENIG gold
        if typ == 'paste':
            return QColor(255, 185, 31, 255)     # exposed pad finish
        if typ == 'silk':
            return QColor(245, 255, 240, 255)    # white silkscreen
        if typ == 'drill':
            return QColor(0, 0, 0, 255)          # real holes
        if typ == 'mechanical':
            lname = (getattr(layer, 'name', '') or '').lower()
            if any(k in lname for k in ('3d', 'body', 'courtyard', 'assembly', 'drawing', 'legend', 'silk')):
                return QColor(245, 255, 240, 255) # white documentation/fill area
        c = QColor(layer.color)
        c.setAlpha(255)
        return c

    def primitive_flat_bounds(self, prim: Primitive) -> QRectF:
        pts = []
        if getattr(prim, 'points', None):
            pts.extend(prim.points)
        if prim.kind == 'region' and getattr(prim, 'contours', None):
            for contour in prim.contours:
                pts.extend(contour)
        if not pts:
            return QRectF()
        xs = [p.x() for p in pts]
        ys = [p.y() for p in pts]
        r = 0.0
        if prim.kind == 'circle':
            r = max(float(getattr(prim, 'radius', 0.0) or 0.0), 0.0)
        elif prim.kind in {'line', 'polyline'}:
            r = max(float(getattr(prim, 'width', 0.0) or 0.0) / 2.0, 0.0)
        elif prim.kind in {'rect', 'obround'} and prim.rect:
            w, h = prim.rect
            c = prim.points[0]
            return QRectF(c.x()-w/2, c.y()-h/2, w, h).normalized()
        elif prim.kind == 'thermal':
            r = max(float(getattr(prim, 'outer_d', 0.0) or 0.0) / 2.0, float(getattr(prim, 'radius', 0.0) or 0.0))
        return QRectF(min(xs)-r, min(ys)-r, (max(xs)-min(xs))+2*r, (max(ys)-min(ys))+2*r).normalized()

    def material_for_primitive(self, prim: Primitive, typ: str, wb: QRectF) -> tuple[QColor, bool]:
        """Return drawing color and whether large filled silk/helper areas should be outline-only.

        Gerber copper layers contain both tracks and flashed pads.  The PNG style
        shows tracks as dark green under soldermask, but exposed pads/vias as gold.
        We therefore classify compact flashed copper primitives as ENIG gold while
        continuous lines/large regions remain dark green.
        """
        solder_green = REALISTIC_TOP_MASK_MID
        track_green = REALISTIC_COPPER_UNDER_MASK
        trace_dark = QColor(10, 87, 14, 255)
        gold = REALISTIC_GOLD_MID
        silk = REALISTIC_SILK
        black = REALISTIC_HOLE
        if typ == 'drill':
            return black, False
        if typ in {'pads', 'paste'}:
            return gold, False
        if typ == 'mask':
            return solder_green, False
        if typ == 'silk':
            # The user's reference bottom render contains a large filled white area.
            # Do NOT outline-filter big silkscreen/legend regions here: draw them
            # filled white exactly like KiCad/3D-view/fabrication-style exports.
            return silk, False
        if typ == 'copper':
            if prim.kind in {'line', 'polyline', 'region'}:
                return track_green, False
            b = self.primitive_flat_bounds(prim)
            span = max(b.width(), b.height())
            area = max(b.width() * b.height(), 0.0)
            # Compact copper flashes are pads/vias -> gold. Large polygons remain
            # dark green so copper pours do not turn the board orange.
            if span <= 7.5 and area <= 45.0:
                return gold, False
            return trace_dark, False
        return QColor(60, 165, 35, 255), False

    def flat_map(self, pt: QPointF, wb: QRectF, scale: float, margin: int) -> QPointF:
        return QPointF(margin + (pt.x() - wb.left()) * scale,
                       margin + (pt.y() - wb.top()) * scale)

    def flat_body_path(self, wb: QRectF, scale: float, margin: int) -> QPainterPath:
        body = self.board_body_path()
        out = QPainterPath()
        out.setFillRule(Qt.FillRule.OddEvenFill)
        try:
            polys = body.toSubpathPolygons()
            if not polys:
                polys = body.toFillPolygons()
            for poly in polys:
                if len(poly) < 3:
                    continue
                out.addPolygon(QPolygonF([self.flat_map(p, wb, scale, margin) for p in poly]))
                out.closeSubpath()
        except Exception:
            out.addRect(QRectF(margin, margin, wb.width() * scale, wb.height() * scale))
        return out

    def build_side_texture(self, side_name: str) -> tuple[QImage, QRectF, int, float]:
        wb = self.board_bounds().normalized()
        # High-resolution cached texture.  It is rebuilt only when layers/mode/window
        # size change, not during rotation, so the 3D stays light but the artwork
        # remains sharp in a large/maximized window.
        margin = 22
        viewport_px = max(self.width(), self.height(), 1200)
        max_px = int(max(3000, min(6200, viewport_px * 2.65)))
        scale = min(max_px / max(wb.width(), 1.0), max_px / max(wb.height(), 1.0))
        scale = max(4.0, min(82.0, scale))
        img_w = max(64, int(math.ceil(wb.width() * scale + 2 * margin)))
        img_h = max(64, int(math.ceil(wb.height() * scale + 2 * margin)))
        img = QImage(img_w, img_h, QImage.Format.Format_ARGB32_Premultiplied)
        img.fill(QColor(0, 0, 0, 0))
        p = QPainter(img)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing, True)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
        p.setClipPath(self.flat_body_path(wb, scale, margin))

        def order(layer):
            typ = self.owner.layer_type_from_info(layer)
            return {'mask': 10, 'copper': 20, 'pads': 25, 'paste': 30, 'mechanical': 38, 'silk': 40, 'drill': 90}.get(typ, 50)

        layers = [l for l in (getattr(self.owner, 'layers', []) or []) if getattr(l, 'visible', True) and self.layer_allowed_for_side(l, side_name)]
        for layer in sorted(layers, key=order):
            typ = self.owner.layer_type_from_info(layer)
            col = self.color_for_layer(layer)
            p.setBrush(QBrush(col))
            p.setPen(Qt.PenStyle.NoPen)
            for prim in getattr(layer, 'primitives', []) or []:
                try:
                    self.draw_flat_primitive(p, prim, typ, wb, scale, margin)
                except Exception:
                    continue
        p.end()
        return img, wb, margin, scale

    def side_texture(self, side_name: str) -> tuple[QImage, QRectF, int, float]:
        key = (self._layers_key(), self.mode, max(self.width(), self.height(), 1200))
        if key != self._texture_cache_key:
            self._texture_cache_key = key
            self._texture_cache = {}
        if side_name not in self._texture_cache:
            self._texture_cache[side_name] = self.build_side_texture(side_name)
        return self._texture_cache[side_name]

    def draw_flat_primitive(self, p: QPainter, prim: Primitive, typ: str, wb: QRectF, scale: float, margin: int):
        def mp(q):
            return self.flat_map(q, wb, scale, margin)

        col, outline_only = self.material_for_primitive(prim, typ, wb)
        p.setBrush(QBrush(col))
        p.setPen(Qt.PenStyle.NoPen)

        # Real plated holes in the 3D texture: gold annular ring on both
        # TOP and BOTTOM textures, then black drill opening.  Previously the
        # drill layer was painted as black only, so some connector holes appeared
        # with green halo but no ENIG/gold ring.
        if typ == 'drill':
            p.setPen(Qt.PenStyle.NoPen)
            if prim.kind == 'circle' and prim.points:
                c = mp(prim.points[0])
                hole_r = max(0.75, prim.radius * scale)
                outer_r = max(hole_r * 1.72, hole_r + 2.2)
                outer_r = min(outer_r, hole_r + 18.0)
                grad = QRadialGradient(c, max(outer_r, 0.001), QPointF(c.x() - outer_r * 0.30, c.y() + outer_r * 0.28))
                grad.setColorAt(0.00, REALISTIC_GOLD_LIGHT)
                grad.setColorAt(0.54, REALISTIC_GOLD_MID)
                grad.setColorAt(1.00, REALISTIC_GOLD_DARK)
                p.setBrush(QBrush(grad))
                p.drawEllipse(c, outer_r, outer_r)
                p.setBrush(QBrush(QColor(18, 45, 10, 255)))
                p.drawEllipse(c, hole_r * 1.10, hole_r * 1.10)
                p.setBrush(QBrush(QColor(0, 0, 0, 255)))
                p.drawEllipse(c, hole_r, hole_r)
                return
            if prim.kind in {'line', 'polyline'} and len(prim.points) >= 2:
                pts = [mp(pt) for pt in prim.points]
                hole_w = max(1.0, prim.width * scale)
                outer_w = max(hole_w * 1.70, hole_w + 4.0)
                outer_w = min(outer_w, hole_w + 36.0)
                p.setBrush(Qt.BrushStyle.NoBrush)
                gold_pen = QPen(REALISTIC_GOLD_MID, outer_w)
                gold_pen.setCapStyle(Qt.PenCapStyle.RoundCap)
                gold_pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
                p.setPen(gold_pen)
                for a, b in zip(pts, pts[1:]):
                    p.drawLine(a, b)
                black_pen = QPen(QColor(0, 0, 0, 255), hole_w)
                black_pen.setCapStyle(Qt.PenCapStyle.RoundCap)
                black_pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
                p.setPen(black_pen)
                for a, b in zip(pts, pts[1:]):
                    p.drawLine(a, b)
                p.setPen(Qt.PenStyle.NoPen)
                return

        if prim.kind in {'line', 'polyline'} and len(prim.points) >= 2:
            w = max(1.0, prim.width * scale)
            if typ == 'silk':
                w = max(1.0, min(w, 2.2))
            pen = QPen(col, w)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            p.setPen(pen)
            pts = [mp(pt) for pt in prim.points]
            for a, b in zip(pts, pts[1:]):
                p.drawLine(a, b)
            p.setPen(Qt.PenStyle.NoPen)
            return

        if prim.kind == 'circle' and prim.points:
            c = mp(prim.points[0])
            rr = max(0.75, prim.radius * scale)
            p.drawEllipse(c, rr, rr)
            return

        if prim.kind in {'rect', 'obround'} and prim.points:
            c = prim.points[0]
            w, h = prim.rect or (0.25, 0.25)
            rect = QRectF(c.x()-w/2, c.y()-h/2, w, h).normalized()
            if prim.kind == 'obround':
                r = min(w, h) / 2.0
                path = QPainterPath()
                mapped = QRectF(margin + (rect.left() - wb.left()) * scale,
                                margin + (rect.top() - wb.top()) * scale,
                                rect.width() * scale, rect.height() * scale)
                path.addRoundedRect(mapped, r * scale, r * scale)
                p.drawPath(path)
            else:
                pts = [QPointF(c.x()-w/2, c.y()-h/2), QPointF(c.x()+w/2, c.y()-h/2),
                       QPointF(c.x()+w/2, c.y()+h/2), QPointF(c.x()-w/2, c.y()+h/2)]
                p.drawPolygon(QPolygonF([mp(x) for x in pts]))
            return

        if prim.kind == 'polygon' and len(prim.points) >= 3:
            poly = QPolygonF([mp(x) for x in prim.points])
            if outline_only:
                pen = QPen(col, 1.4)
                pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
                p.setPen(pen)
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawPolygon(poly)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QBrush(col))
            else:
                p.drawPolygon(poly)
            return

        if prim.kind == 'region' and prim.contours:
            path = QPainterPath()
            path.setFillRule(Qt.FillRule.OddEvenFill)
            for contour in prim.contours:
                if len(contour) >= 3:
                    path.addPolygon(QPolygonF([mp(x) for x in contour]))
                    path.closeSubpath()
            if outline_only:
                pen = QPen(col, 1.3)
                pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
                p.setPen(pen)
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawPath(path)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QBrush(col))
            else:
                p.drawPath(path)
            return

        if prim.kind == 'thermal' and prim.points:
            c = mp(prim.points[0])
            od = float(getattr(prim, 'outer_d', prim.radius * 2.0) or prim.radius * 2.0)
            rr = max(1.0, od * scale / 2.0)
            p.drawEllipse(c, rr, rr)

    def projected_body_path(self, z: float) -> QPainterPath:
        body = self.board_body_path()
        out = QPainterPath()
        out.setFillRule(Qt.FillRule.OddEvenFill)
        try:
            polys = body.toSubpathPolygons()
            if not polys:
                polys = body.toFillPolygons()
            for poly in polys:
                if len(poly) < 3:
                    continue
                out.addPolygon(QPolygonF([self.project(pt.x(), pt.y(), z) for pt in poly]))
                out.closeSubpath()
        except Exception:
            wb = self.board_bounds()
            corners = [QPointF(wb.left(), wb.top()), QPointF(wb.right(), wb.top()), QPointF(wb.right(), wb.bottom()), QPointF(wb.left(), wb.bottom())]
            out.addPolygon(QPolygonF([self.project(c.x(), c.y(), z) for c in corners]))
            out.closeSubpath()
        return out

    def draw_board_body(self, p: QPainter, wb: QRectF):
        half = self.board_thickness_mm / 2.0
        top_z, bot_z = half, -half
        body = self.board_body_path()
        faces = []
        try:
            polys = body.toSubpathPolygons()
            if not polys:
                polys = body.toFillPolygons()
            for poly in polys:
                if len(poly) < 2:
                    continue
                pts = list(poly)
                if pts[0] != pts[-1]:
                    pts.append(pts[0])
                for a, b in zip(pts, pts[1:]):
                    if math.hypot(a.x() - b.x(), a.y() - b.y()) < 1e-6:
                        continue
                    wall = QPolygonF([self.project(a.x(), a.y(), top_z), self.project(b.x(), b.y(), top_z),
                                      self.project(b.x(), b.y(), bot_z), self.project(a.x(), a.y(), bot_z)])
                    depth = (self.camera_depth(a.x(), a.y(), top_z) + self.camera_depth(b.x(), b.y(), top_z) +
                             self.camera_depth(b.x(), b.y(), bot_z) + self.camera_depth(a.x(), a.y(), bot_z)) / 4.0
                    faces.append((depth, 'wall', wall))
        except Exception:
            pass
        c = wb.center()
        faces.append((self.camera_depth(c.x(), c.y(), top_z), 'top', self.projected_body_path(top_z)))
        faces.append((self.camera_depth(c.x(), c.y(), bot_z), 'bottom', self.projected_body_path(bot_z)))
        for _depth, kind, geom in sorted(faces, key=lambda x: x[0]):
            if kind == 'wall':
                p.setBrush(QBrush(QColor(8, 92, 11, 255)))
                p.setPen(QPen(QColor(72, 198, 58, 255), 0.8))
                p.drawPolygon(geom)
            elif kind == 'top':
                p.setBrush(QBrush(QColor(44, 168, 22, 255)))
                p.setPen(QPen(QColor(111, 214, 80, 255), 0.9))
                p.drawPath(geom)
            else:
                p.setBrush(QBrush(QColor(34, 155, 18, 255)))
                p.setPen(QPen(QColor(91, 205, 70, 255), 0.9))
                p.drawPath(geom)

    def draw_side_texture_3d(self, p: QPainter, side_name: str, z: float):
        img, wb, margin, scale = self.side_texture(side_name)
        # The texture includes a margin around the Edge.Cuts bbox. Map that full
        # image rectangle to the same physical board plane, expanded by margin/scale.
        left = wb.left() - margin / scale
        top = wb.top() - margin / scale
        right = wb.right() + margin / scale
        bottom = wb.bottom() + margin / scale
        p0 = self.project(left, top, z)
        p1 = self.project(right, top, z)
        p3 = self.project(left, bottom, z)
        iw, ih = max(1, img.width()), max(1, img.height())
        tr = QTransform((p1.x() - p0.x()) / iw, (p1.y() - p0.y()) / iw,
                        (p3.x() - p0.x()) / ih, (p3.y() - p0.y()) / ih,
                        p0.x(), p0.y())
        p.save()
        p.setClipPath(self.projected_body_path(z), Qt.ClipOperation.IntersectClip)
        p.setTransform(tr, False)
        p.drawImage(0, 0, img)
        p.restore()

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing, not self.fast_interaction)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing, True)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform, True)
        p.fillRect(self.rect(), QColor(0, 0, 0))
        if not getattr(self.owner, 'layers', []):
            p.setPen(QColor(220, 240, 255))
            p.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "Open Gerber/Drill files first, then use 3D view.")
            return
        wb = self.board_bounds()
        self._paint_center = wb.center()
        half = self.board_thickness_mm / 2.0
        c = wb.center()
        top_depth = self.camera_depth(c.x(), c.y(), half)
        bottom_depth = self.camera_depth(c.x(), c.y(), -half)
        near = 'top' if top_depth >= bottom_depth else 'bottom'
        far = 'bottom' if near == 'top' else 'top'

        # Draw far artwork first, then opaque board, then near artwork. This makes
        # the PCB solid: no transparency and no opposite-side bleed-through.
        if self.mode in {'both', 'copper', far}:
            self.draw_side_texture_3d(p, far, -half if far == 'bottom' else half)
        self.draw_board_body(p, wb)
        if self.mode in {'both', 'copper', near}:
            self.draw_side_texture_3d(p, near, half if near == 'top' else -half)
        self.draw_overlay(p)

    def draw_overlay(self, p: QPainter):
        p.setPen(QColor(210, 235, 255))
        p.setFont(QFont('Segoe UI', 10, QFont.Weight.Bold))
        txt = f"HIGH-RES REALISTIC PCB | Edge.Cuts solid {self.board_thickness_mm:.1f} mm | white silkscreen/fill ON | left rotate | right pan | wheel zoom | F fit"
        p.drawText(14, 24, txt)

    def mousePressEvent(self, e: QMouseEvent):
        self.last_mouse = e.position()
        self.rotating = e.button() == Qt.MouseButton.LeftButton
        self.panning = e.button() in {Qt.MouseButton.RightButton, Qt.MouseButton.MiddleButton}

    def mouseMoveEvent(self, e: QMouseEvent):
        delta = e.position() - self.last_mouse
        self.last_mouse = e.position()
        if self.rotating:
            self._start_fast_interaction()
            self.rot_z = (self.rot_z + delta.x() * 0.45) % 360.0
            self.rot_x = (self.rot_x + delta.y() * 0.45) % 360.0
            self.angle = self.rot_z
            self.tilt = self.rot_x
            self.update()
        elif self.panning:
            self._start_fast_interaction()
            self.pan += QPointF(delta.x(), delta.y())
            self.update()

    def mouseReleaseEvent(self, e: QMouseEvent):
        self.rotating = False
        self.panning = False
        self._quality_timer.start(35)

    def wheelEvent(self, e: QWheelEvent):
        self._start_fast_interaction()
        factor = 1.15 if e.angleDelta().y() > 0 else 1 / 1.15
        self.zoom = max(0.5, min(320.0, self.zoom * factor))
        self.update()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        # Rebuild only the cached TOP/BOTTOM textures so a larger window gets
        # higher-resolution artwork.  Camera/geometry cache remains intact.
        self._texture_cache_key = None
        self._texture_cache = {}
        self.update()

    def keyPressEvent(self, e):
        if e.key() == Qt.Key.Key_F:
            self.fit()
        elif e.key() == Qt.Key.Key_R:
            self.rot_x, self.rot_y, self.rot_z = -58.0, 0.0, -35.0
            self.angle, self.tilt, self.pan = self.rot_z, self.rot_x, QPointF(0, 0)
            self.update()


class PCB3DDialog(QDialog):
    def __init__(self, owner: MainWindow):
        super().__init__(owner)
        self.setWindowTitle("ULTRA GERBER VIEWER - 3D PCB")
        self.setWindowFlags(self.windowFlags() | Qt.WindowType.WindowMaximizeButtonHint | Qt.WindowType.WindowMinimizeButtonHint)
        self.setMinimumSize(1250, 780)
        try:
            geo = QApplication.primaryScreen().availableGeometry()
            self.resize(int(geo.width() * 0.92), int(geo.height() * 0.88))
        except Exception:
            self.resize(1600, 950)
        self.viewer = PCB3DWidget(owner, self)
        topbar = QHBoxLayout()
        mode = QComboBox()
        mode.addItems(["Both Sides", "Top Side", "Bottom Side", "Copper Only"])
        mode.currentTextChanged.connect(lambda t: self.viewer.set_mode({
            "Both Sides": "both", "Top Side": "top", "Bottom Side": "bottom", "Copper Only": "copper"
        }[t]))
        fit = QPushButton("FIT")
        fit.clicked.connect(self.viewer.fit)
        reset = QPushButton("RESET CAMERA")
        reset.clicked.connect(lambda: (setattr(self.viewer, 'rot_x', -58.0), setattr(self.viewer, 'rot_y', 0.0), setattr(self.viewer, 'rot_z', -35.0), setattr(self.viewer, 'angle', -35.0), setattr(self.viewer, 'tilt', -58.0), setattr(self.viewer, 'pan', QPointF(0,0)), setattr(self.viewer, 'zoom', 1.0), self.viewer.fit()))
        board = QCheckBox("Board body")
        board.setChecked(True)
        board.toggled.connect(lambda v: (setattr(self.viewer, 'show_board', bool(v)), self.viewer.update()))
        topbar.addWidget(QLabel("3D Mode:"))
        topbar.addWidget(mode)
        topbar.addWidget(board)
        topbar.addStretch(1)
        topbar.addWidget(fit)
        topbar.addWidget(reset)
        lay = QVBoxLayout(self)
        lay.addLayout(topbar)
        lay.addWidget(self.viewer, 1)
        QTimer.singleShot(50, self.viewer.fit)


_ugv_original_menu = MainWindow.menu

def _ugv_menu_with_3d(self):
    _ugv_original_menu(self)
    menu_3d = self.menuBar().addMenu("3D")
    open3d = QAction("Open 3D PCB Viewer", self)
    open3d.setShortcut("Ctrl+3")
    open3d.triggered.connect(lambda _=False: self.open_3d_viewer("both"))
    menu_3d.addAction(open3d)
    menu_3d.addSeparator()
    for title, mode in (("3D Both Sides", "both"), ("3D Top Side", "top"), ("3D Bottom Side", "bottom"), ("3D Copper Only", "copper")):
        act = QAction(title, self)
        act.triggered.connect(lambda _=False, m=mode: self.open_3d_viewer(m))
        menu_3d.addAction(act)


def _ugv_open_3d_viewer(self, mode: str = "both"):
    # QAction.triggered passes a checked bool; normalize it so mode is always text.
    if not isinstance(mode, str):
        mode = "both"
    mode = mode.lower()
    if mode not in {"both", "top", "bottom", "copper"}:
        mode = "both"
    if not getattr(self, 'layers', None):
        self.log_msg("3D: πρώτα άνοιξε Gerber/Drill αρχεία.")
        return
    dlg = getattr(self, '_pcb3d_dialog', None)
    if dlg is None or not dlg.isVisible():
        dlg = PCB3DDialog(self)
        self._pcb3d_dialog = dlg
    dlg.viewer.set_mode(mode)
    dlg.show()
    dlg.raise_()
    dlg.activateWindow()
    QTimer.singleShot(60, dlg.viewer.fit)
    self.log_msg(f"3D viewer opened: {mode.upper()} accelerated rendering from current parsed layers.")

MainWindow.menu = _ugv_menu_with_3d
MainWindow.open_3d_viewer = _ugv_open_3d_viewer


# -----------------------------------------------------------------------------
# FINAL Altium drill TXT registration fix
# -----------------------------------------------------------------------------
# Altium exports real NC drill files as text files such as
#   *RoundHoles-Plated.TXT
#   *SlotHoles-Plated.TXT
# These are not drill legends/tables.  Older heuristics treated every .TXT as a
# helper/table layer, so SlotHoles/RoundHoles bypassed the PCB outlier filter and
# stayed at the Altium absolute NC origin.  The code below treats these files as
# real drill layers and performs a stronger pad-registration pass.

_UGV_PREV_IS_DRILL_LEGEND_OR_TABLE = RasterRenderer.is_drill_legend_or_table_layer_name

def _ugv_is_drill_legend_or_table_layer_name_final(name: str) -> bool:
    n = str(name).lower().replace('\\', '/')
    base = n.rsplit('/', 1)[-1]
    # Real Altium NC drill exports.  They must be aligned to pads, not rendered
    # as remote helper drawings.
    if any(tok in base for tok in (
        'roundholes-plated', 'roundholes-nonplated', 'slotholes-plated', 'slotholes-nonplated',
        'round_holes', 'slot_holes', 'roundholes', 'slotholes'
    )):
        return False
    # Only report/legend/table TXT files are helper layers.  Do not blanket-match .txt.
    if base.endswith('.txt'):
        return any(tok in base for tok in (
            'read', 'readme', 'report', 'legend', 'table', 'chart', 'map', 'drawing', 'status', 'transcode'
        ))
    return _UGV_PREV_IS_DRILL_LEGEND_OR_TABLE(name)

RasterRenderer.is_drill_legend_or_table_layer_name = staticmethod(_ugv_is_drill_legend_or_table_layer_name_final)


def _ugv_drill_bbox_and_points(layer):
    drills = []
    for prim in getattr(layer, 'primitives', []) or []:
        if prim.kind == 'circle' and prim.points:
            c = prim.points[0]
            drills.append((c.x(), c.y(), max(float(prim.radius) * 2.0, 0.05)))
        elif prim.kind == 'line' and len(prim.points) >= 2:
            p1, p2 = prim.points[0], prim.points[1]
            d = max(float(getattr(prim, 'width', 0.0) or 0.0), 0.05)
            drills.append((p1.x(), p1.y(), d))
            drills.append((p2.x(), p2.y(), d))
        elif prim.kind == 'polyline' and len(prim.points) >= 2:
            d = max(float(getattr(prim, 'width', 0.0) or 0.0), 0.05)
            for pt in prim.points:
                drills.append((pt.x(), pt.y(), d))
    return drills


def _ugv_move_layer_geometry_final(layer, dx: float, dy: float):
    def mv(pt):
        pt.setX(pt.x() + dx)
        pt.setY(pt.y() + dy)
    for prim in getattr(layer, 'primitives', []) or []:
        for pt in getattr(prim, 'points', []) or []:
            mv(pt)
        for contour in getattr(prim, 'contours', None) or []:
            for pt in contour:
                mv(pt)
        for attr in ('_fast_path_cache', '_solid_stroke_cache', '_solid_stroke_cache_key', '_fast_region_path_cache', '_fast_polygon_cache'):
            if hasattr(prim, attr):
                try: delattr(prim, attr)
                except Exception: pass
    for attr in ('_fast_bounds_cache', '_viewport_candidate_cache'):
        if hasattr(layer, attr):
            try: delattr(layer, attr)
            except Exception: pass


def _ugv_prim_pad_center_size_final(prim):
    try:
        if prim.kind == 'circle' and prim.points:
            c = prim.points[0]
            return c.x(), c.y(), max(float(prim.radius) * 2.0, 0.05)
        if prim.kind in ('rect', 'obround') and prim.points:
            c = prim.points[0]
            w, h = prim.rect or (0.0, 0.0)
            return c.x(), c.y(), max(float(w), float(h), 0.05)
        if prim.kind == 'polygon' and len(prim.points) >= 3:
            b = QPolygonF(prim.points).boundingRect().normalized()
            if b.width() <= 10.0 and b.height() <= 10.0:
                c = b.center()
                return c.x(), c.y(), max(b.width(), b.height(), 0.05)
        if prim.kind == 'region' and getattr(prim, 'contours', None):
            path = QPainterPath()
            first = True
            for cont in prim.contours:
                if not cont: continue
                if first:
                    path.moveTo(cont[0]); first = False
                else:
                    path.moveTo(cont[0])
                for pt in cont[1:]: path.lineTo(pt)
            b = path.boundingRect().normalized()
            if b.width() <= 10.0 and b.height() <= 10.0:
                c = b.center()
                return c.x(), c.y(), max(b.width(), b.height(), 0.05)
    except Exception:
        return None
    return None


def _ugv_auto_align_outside_drill_layers_final(self):
    # First run the previous aligner; then repair the remaining Altium TXT drill
    # clouds that are still outside the board.
    try:
        _UGV_PREV_AUTO_ALIGN_OUTSIDE_DRILL_LAYERS(self)
    except Exception as e:
        try: self.log_msg(f'Previous drill aligner warning: {e}')
        except Exception: pass

    if not getattr(self, 'layers', None):
        return

    board_ref = self.renderer.main_board_reference(self.layers).normalized()
    if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
        board_ref = self.renderer.bounds([l for l in self.layers if getattr(l, 'visible', True)]).normalized()
    if not board_ref.isValid() or board_ref.width() <= 0 or board_ref.height() <= 0:
        return
    board_ext = QRectF(board_ref).adjusted(-8.0, -8.0, 8.0, 8.0)

    targets = []
    for layer in self.layers:
        typ = str(getattr(layer, 'layer_type', '')).lower()
        if typ in {'drill', 'drillmap', 'mechanical', 'assembly', '3d'}:
            continue
        lname = layer.name.lower()
        if not any(k in lname for k in ('copper', 'pad', 'signal', 'top', 'bottom')):
            continue
        for prim in getattr(layer, 'primitives', []) or []:
            cs = _ugv_prim_pad_center_size_final(prim)
            if not cs: continue
            x, y, sz = cs
            if 0.10 <= sz <= 9.0 and board_ext.contains(QPointF(x, y)):
                targets.append((x, y, sz))
    if len(targets) < 4:
        return

    cell = 0.45
    grid = {}
    for x, y, sz in targets:
        grid.setdefault((int(round(x / cell)), int(round(y / cell))), []).append((x, y, sz))

    def hit(x, y, dia):
        gx, gy = int(round(x / cell)), int(round(y / cell))
        tol = max(0.20, min(1.10, dia * 1.10))
        t2 = tol * tol
        for ix in range(gx - 3, gx + 4):
            for iy in range(gy - 3, gy + 4):
                for px, py, psz in grid.get((ix, iy), ()): 
                    if psz + 0.35 < dia:
                        continue
                    dx = x - px; dy = y - py
                    if dx * dx + dy * dy <= t2:
                        return True
        return False

    for layer in self.layers:
        if str(getattr(layer, 'layer_type', '')).lower() != 'drill':
            continue
        lname = layer.name.lower()
        is_altium_txt = any(tok in lname for tok in ('roundholes', 'slotholes', 'slot_holes', 'round_holes'))
        drills = _ugv_drill_bbox_and_points(layer)
        if not drills:
            continue
        b = self.renderer.layer_bounds(layer).normalized()
        if not b.isValid():
            continue
        already = sum(1 for x, y, d in drills if hit(x, y, d))
        outside = not board_ext.intersects(b) and not board_ext.contains(b.center())
        if already >= max(3, int(len(drills) * 0.35)) and not outside:
            continue

        # Strong exhaustive vote.  This is intentionally for the small Altium NC
        # TXT files too; SlotHoles may only have a handful of endpoints.
        q = 0.01
        votes = {}
        d_sample = drills[:300]
        for dx0, dy0, dd in d_sample:
            for px, py, psz in targets:
                if psz + 0.35 < dd:
                    continue
                dx = px - dx0; dy = py - dy0
                # Altium NC absolute origins can be hundreds of mm away; accept
                # that, but reject insane drawings/reports.
                if abs(dx) > 1500.0 or abs(dy) > 1500.0:
                    continue
                key = (round(dx / q), round(dy / q))
                votes[key] = votes.get(key, 0) + 1
        if not votes:
            continue
        best = None
        for key, vote in sorted(votes.items(), key=lambda kv: kv[1], reverse=True)[:180]:
            dx = key[0] * q; dy = key[1] * q
            hits = sum(1 for x, y, d in drills if hit(x + dx, y + dy, d))
            ratio = hits / max(len(drills), 1)
            # Small drill files need an absolute hit count rule; large drill files
            # need ratio too.  Distance is only a tie-breaker.
            score = (hits, ratio, vote, -math.hypot(dx, dy))
            if best is None or score > best[0]:
                best = (score, dx, dy, hits, ratio)
        if not best:
            continue
        _, dx, dy, hits, ratio = best
        needed = 2 if len(drills) <= 12 else max(4, int(len(drills) * 0.12))
        if is_altium_txt:
            needed = min(needed, 3)
        if hits < needed or hits <= already:
            # Last safety fallback for Altium TXT only: if it is still completely
            # outside, move the cloud near the board center instead of letting it
            # pollute the canvas.  This fallback is visible in INFO so it cannot
            # be confused with pad-verified alignment.
            if is_altium_txt and outside:
                dx = board_ref.center().x() - b.center().x()
                dy = board_ref.center().y() - b.center().y()
                _ugv_move_layer_geometry_final(layer, dx, dy)
                layer.bbox = self.renderer.layer_bounds(layer)
                layer.info = f'CENTERED ALTIUM DRILL TXT dx={dx:.3f} dy={dy:.3f} mm | ' + layer.info
                try: self.log_msg(f'CENTERED Altium TXT drill layer {layer.name}: dx={dx:.3f} dy={dy:.3f} mm')
                except Exception: pass
            continue
        if abs(dx) < 0.005 and abs(dy) < 0.005:
            continue
        _ugv_move_layer_geometry_final(layer, dx, dy)
        layer.bbox = self.renderer.layer_bounds(layer)
        layer.info = f'FINAL PAD-MATCHED ALTIUM DRILL dx={dx:.3f} dy={dy:.3f} mm hits={hits}/{len(drills)} | ' + layer.info
        try: self.log_msg(f'FINAL PAD-MATCHED Altium drill layer {layer.name}: dx={dx:.3f} dy={dy:.3f} mm hits={hits}/{len(drills)}')
        except Exception: pass

    try:
        self.populate_table()
    except Exception:
        pass


_UGV_PREV_AUTO_ALIGN_OUTSIDE_DRILL_LAYERS = MainWindow.auto_align_outside_drill_layers
MainWindow.auto_align_outside_drill_layers = _ugv_auto_align_outside_drill_layers_final

def main():
    app = QApplication(sys.argv)
    app.setApplicationName("ULTRA GERBER VIEWER by George Kourtidis")
    w = MainWindow()
    w.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
