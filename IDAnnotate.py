"""
Rahat Label Studio v2
Identity-aware video/image annotation desktop application.

Core concepts:
- Class = semantic category (child, teacher, person, etc.)
- Individual ID = persistent identity within the project
- Track ID = optional tracker-generated local ID
- One annotation = frame + class + individual ID + bbox

This version intentionally uses lightweight dependencies:
Tkinter + OpenCV + Pillow.
"""

import json
import math
import random
import shutil
import subprocess
import sys
import time
from pathlib import Path
import tkinter as tk
import tkinter.font as tkfont
from tkinter import ttk, filedialog, messagebox, simpledialog

import cv2
import numpy as np
from PIL import Image, ImageTk, ImageDraw, ImageFont


APP_NAME = "IDAnnotate --by Md. Rahatul Islam"   # <- change the app name here
PROJECT_VERSION = 1

# Paths work both when running the .py file and when packaged as a Windows .exe.
if getattr(sys, "frozen", False):
    APP_DIR = Path(sys.executable).resolve().parent             # folder of the .exe
    BUNDLE_DIR = Path(getattr(sys, "_MEIPASS", APP_DIR))        # bundled data files
else:
    APP_DIR = Path(__file__).resolve().parent
    BUNDLE_DIR = APP_DIR

# Logo: put "logo.png" (and optionally "logo.ico") next to the app, or use
# View > Change Logo...
DEFAULT_LOGO = (
    APP_DIR / r"D:\IDAnnotate\logo.png" if (APP_DIR / r"D:\IDAnnotate\logo.png").exists()
    else BUNDLE_DIR / r"D:\IDAnnotate\logo.png"
)
LOGO_ICO = (
    APP_DIR / r"D:\IDAnnotate\logo.ico" if (APP_DIR / r"D:\IDAnnotate\logo.ico").exists()
    else BUNDLE_DIR / r"D:\IDAnnotate\logo.ico"
)
SETTINGS_FILE = APP_DIR / "rahat_settings.json"

# ---------------- Theme (change colours here) ----------------
THEME = {
    "bg":           "#0d1020",   # window / toolbar
    "panel":        "#141934",   # side panels
    "card":         "#1b2145",   # menus, dialogs
    "field":        "#0b0f21",   # list boxes, entries
    "border":       "#2b3367",
    "text":         "#e9ecff",
    "muted":        "#8e97c8",
    "accent":       "#6c5ce7",   # primary buttons
    "accent_hover": "#8174f0",
    "accent2":      "#22d3ee",   # headings / highlights
    "btn":          "#232b57",
    "btn_hover":    "#2f3a73",
    "select":       "#3a46a8",
    "backdrop_top":    "#1a1f4a",
    "backdrop_bottom": "#070914",
}


def _hex_rgb(h):
    h = h.lstrip("#")
    return int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)


def _rgb_hex(rgb):
    return "#%02x%02x%02x" % tuple(int(max(0, min(255, v))) for v in rgb)


def make_backdrop(w, h):
    """Soft gradient + glow + faint dot grid, used behind the video frame."""
    w, h = max(2, int(w)), max(2, int(h))
    top = np.array(_hex_rgb(THEME["backdrop_top"]), dtype=np.float32)
    bottom = np.array(_hex_rgb(THEME["backdrop_bottom"]), dtype=np.float32)
    glow_rgb = np.array(_hex_rgb(THEME["accent"]), dtype=np.float32) * 0.28

    ys = np.linspace(0.0, 1.0, h, dtype=np.float32)[:, None]
    xs = np.linspace(0.0, 1.0, w, dtype=np.float32)[None, :]

    img = top + (bottom - top) * ys[..., None]                 # vertical gradient
    dist = np.sqrt(((xs - 0.5) * 1.3) ** 2 + (ys - 0.30) ** 2)  # radial glow
    glow = np.clip(1.0 - dist / 0.85, 0.0, 1.0) ** 2
    img = img + glow[..., None] * glow_rgb
    img[::30, ::30] += 16                                        # dot grid
    return Image.fromarray(np.clip(img, 0, 255).astype(np.uint8), "RGB")


class RahatLabelStudio(tk.Tk):
    def __init__(self):
        super().__init__()

        self.title(APP_NAME)
        self.geometry("1500x920")
        self.minsize(1150, 700)

        # ---------------- Theme state ----------------
        self._bg_photo = None
        self._bg_key = None
        self._resize_job = None
        self._welcome_logo = None
        self._welcome_logo_path = None
        self._welcome_btns = []
        self._apply_theme()

        # ---------------- Logo / settings ----------------
        self.logo_path = None
        self._logo_img = None
        self._icon_img = None
        self.logo_label = None
        self.load_settings()

        # ---------------- Media ----------------
        self.media_type = None
        self.video_path = None
        self.image_paths = []
        self.cap = None
        self.total_frames = 0
        self.fps = 25.0
        self.frame_idx = 0
        self.frame_bgr = None

        # ---------------- Project ----------------
        self.project_file = None
        self.project_dir = None
        self.project_name = "Untitled"

        # class_id -> class record
        self.classes = {
            0: {"name": "person"}
        }

        # individual_id -> identity record
        self.identities = {}

        # frame index -> annotation list
        # {
        #   class_id, individual_id, track_id,
        #   bbox, occluded, visibility, confidence
        # }
        self.annotations = {}

        self.next_individual_id = 1
        self.next_track_id = 1

        # ---------------- UI state ----------------
        self.active_class_id = 0
        self.active_individual_id = 1
        self.selected_index = None

        self.current_boxes = []

        self.photo = None
        self.scale = 1.0
        self.offset = (0, 0)

        self.drag_mode = None
        self.drag_start_canvas = None
        self.drag_start_frame = None
        self.drag_box_index = None
        self.original_bbox = None
        self.resize_handle = None
        self.handle_radius = 10

        self.playing = False
        self.propagating = False

        self.id_colors = [
            "#ff4d4d", "#4da6ff", "#35c46b", "#f2c94c",
            "#a970ff", "#ff8a3d", "#00b8a9", "#e85aad",
            "#8e9aa7", "#27ae60", "#d68910", "#2980b9",
            "#c0392b", "#16a085", "#7d3c98", "#7f8c8d"
        ]

        self._build_menu()
        self._build_ui()
        self._bind_keys()

        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.apply_logo()
        self.after(200, self.redraw)
        self.update_status()

    # ============================================================
    # THEME / BACKDROP / WELCOME SCREEN
    # ============================================================

    def _apply_theme(self):
        t = THEME
        self.configure(bg=t["bg"])

        for fname in ("TkDefaultFont", "TkTextFont", "TkMenuFont"):
            try:
                tkfont.nametofont(fname).configure(size=10)
            except tk.TclError:
                pass
        fam = tkfont.nametofont("TkDefaultFont").actual("family")
        self.ui_family = fam
        self.title_font = tkfont.Font(family=fam, size=40, weight="bold")
        self.tag_font = tkfont.Font(family=fam, size=13)
        self.small_font = tkfont.Font(family=fam, size=10)

        # Classic Tk widgets (Listbox, Menu, Canvas) are themed via the option DB.
        opt = self.option_add
        opt("*Listbox.background", t["field"])
        opt("*Listbox.foreground", t["text"])
        opt("*Listbox.selectBackground", t["select"])
        opt("*Listbox.selectForeground", "#ffffff")
        opt("*Listbox.highlightThickness", 1)
        opt("*Listbox.highlightBackground", t["border"])
        opt("*Listbox.highlightColor", t["accent"])
        opt("*Listbox.borderWidth", 0)
        opt("*Listbox.relief", "flat")
        opt("*Listbox.activestyle", "none")
        opt("*Menu.background", t["card"])
        opt("*Menu.foreground", t["text"])
        opt("*Menu.activeBackground", t["accent"])
        opt("*Menu.activeForeground", "#ffffff")
        opt("*Menu.borderWidth", 0)
        opt("*Menu.relief", "flat")
        opt("*Canvas.highlightThickness", 0)

        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        style.configure(
            ".",
            background=t["panel"], foreground=t["text"],
            bordercolor=t["border"], lightcolor=t["panel"], darkcolor=t["panel"],
            troughcolor=t["field"], focuscolor=t["accent"],
        )
        style.configure("TFrame", background=t["panel"])
        style.configure("Top.TFrame", background=t["bg"])
        style.configure("TLabel", background=t["panel"], foreground=t["text"])
        style.configure("Top.TLabel", background=t["bg"], foreground=t["text"])
        style.configure(
            "Header.TLabel", background=t["panel"], foreground=t["accent2"],
            font=(fam, 10, "bold"),
        )
        style.configure(
            "Status.TLabel", background="#090c1a", foreground=t["muted"],
            padding=(12, 5),
        )

        def button(name, bg, hover, pressed, fg="#ffffff", pad=(10, 5)):
            style.configure(
                name, background=bg, foreground=fg, bordercolor=bg,
                lightcolor=bg, darkcolor=bg, relief="flat", padding=pad,
                focusthickness=0, focuscolor=bg,
            )
            style.map(
                name,
                background=[("pressed", pressed), ("active", hover)],
                lightcolor=[("pressed", pressed), ("active", hover)],
                darkcolor=[("pressed", pressed), ("active", hover)],
                bordercolor=[("pressed", pressed), ("active", hover)],
                foreground=[("disabled", t["muted"])],
            )

        button("TButton", t["btn"], t["btn_hover"], t["accent"], fg=t["text"])
        button("Tool.TButton", t["btn"], t["btn_hover"], t["accent"], fg=t["text"], pad=(8, 5))
        button("Accent.TButton", t["accent"], t["accent_hover"], "#5546d6")
        button("Tool.Accent.TButton", t["accent"], t["accent_hover"], "#5546d6", pad=(8, 5))
        button("Hero.Accent.TButton", t["accent"], t["accent_hover"], "#5546d6", pad=(18, 10))
        button("Hero.TButton", t["btn"], t["btn_hover"], t["accent"], fg=t["text"], pad=(18, 10))

        style.configure(
            "TEntry", fieldbackground=t["field"], foreground=t["text"],
            insertcolor=t["text"], bordercolor=t["border"],
            lightcolor=t["field"], darkcolor=t["field"], padding=4,
        )
        style.map("TEntry", bordercolor=[("focus", t["accent"])])
        style.configure(
            "Horizontal.TScale", background=t["accent"], troughcolor=t["field"],
            bordercolor=t["border"], lightcolor=t["accent"], darkcolor=t["accent"],
        )
        style.configure("TSeparator", background=t["border"])
        style.configure("TPanedwindow", background=t["bg"])
        try:
            style.configure("Sash", sashthickness=6, gripcount=0, background=t["bg"])
        except tk.TclError:
            pass
        style.configure(
            "Horizontal.TProgressbar", background=t["accent"], troughcolor=t["field"],
            bordercolor=t["border"], lightcolor=t["accent"], darkcolor=t["accent"],
        )

    def _draw_accent_strip(self, _event=None):
        c = self.accent_strip
        w = max(2, c.winfo_width())
        c.delete("all")
        a, b = _hex_rgb(THEME["accent"]), _hex_rgb(THEME["accent2"])
        steps = 72
        for i in range(steps):
            f = i / (steps - 1)
            col = _rgb_hex([a[k] + (b[k] - a[k]) * f for k in range(3)])
            c.create_rectangle(
                int(i * w / steps), 0, int((i + 1) * w / steps) + 1, 3,
                fill=col, outline="",
            )

    def _on_canvas_resize(self, _event=None):
        if self._resize_job is not None:
            try:
                self.after_cancel(self._resize_job)
            except Exception:
                pass
        self._resize_job = self.after(60, self.redraw)

    def _draw_canvas_backdrop(self, cw, ch):
        key = (cw, ch)
        if self._bg_key != key or self._bg_photo is None:
            self._bg_photo = ImageTk.PhotoImage(make_backdrop(cw, ch))
            self._bg_key = key
        self.canvas.create_image(0, 0, anchor="nw", image=self._bg_photo)

    def _get_welcome_logo(self):
        path = self.logo_path
        if not path or not Path(path).exists():
            self._welcome_logo = None
            self._welcome_logo_path = None
            return None
        if self._welcome_logo is not None and self._welcome_logo_path == path:
            return self._welcome_logo
        try:
            img = Image.open(path).convert("RGBA")
            img.thumbnail((110, 110), Image.Resampling.LANCZOS)
            self._welcome_logo = ImageTk.PhotoImage(img)
            self._welcome_logo_path = path
        except Exception:
            self._welcome_logo = None
            self._welcome_logo_path = None
        return self._welcome_logo

    def _draw_welcome(self):
        c = self.canvas
        cw, ch = c.winfo_width(), c.winfo_height()
        if cw < 80 or ch < 80:
            return

        t = THEME
        self._draw_canvas_backdrop(cw, ch)

        cx = cw // 2
        base = int(ch * 0.46)
        logo = self._get_welcome_logo()
        if logo is not None:
            c.create_image(cx, base - 150, image=logo)
        else:
            base -= 45

        name, credit = APP_NAME, ""
        if "--" in APP_NAME:
            name, credit = [p.strip() for p in APP_NAME.split("--", 1)]

        ty = base - 70
        if name.startswith("ID") and len(name) > 2:
            rest = name[2:]
            w1 = self.title_font.measure("ID")
            w2 = self.title_font.measure(rest)
            x0 = cx - (w1 + w2) // 2
            c.create_text(x0, ty, text="ID", anchor="w",
                          font=self.title_font, fill=t["accent2"])
            c.create_text(x0 + w1, ty, text=rest, anchor="w",
                          font=self.title_font, fill="#ffffff")
        else:
            c.create_text(cx, ty, text=name, font=self.title_font, fill="#ffffff")

        if credit:
            c.create_text(cx, base - 30, text=credit,
                          font=self.small_font, fill=t["muted"])
        c.create_text(cx, base + 2, text="Identity-aware video & image annotation",
                      font=self.tag_font, fill=t["text"])

        c.create_window(cx, base + 58, window=self._welcome_btns[0], width=250)
        c.create_window(cx, base + 106, window=self._welcome_btns[1], width=250)

        c.create_text(
            cx, base + 162,
            text="Draw boxes   •   lock persistent IDs   •   track forward   •   "
                 "export YOLO / COCO / MOT / annotated video",
            font=self.small_font, fill=t["muted"],
        )

    # ============================================================
    # LOGO / SETTINGS
    # ============================================================

    def load_settings(self):
        path = None
        try:
            if SETTINGS_FILE.exists():
                data = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
                path = data.get("logo_path")
        except Exception:
            path = None

        if path and Path(path).exists():
            self.logo_path = path
        elif DEFAULT_LOGO.exists():
            self.logo_path = str(DEFAULT_LOGO)

    def save_settings(self):
        try:
            SETTINGS_FILE.write_text(
                json.dumps({"logo_path": self.logo_path}, indent=2),
                encoding="utf-8"
            )
        except Exception:
            pass

    def apply_logo(self):
        """Apply the logo to the window icon and the top toolbar."""
        if self.logo_label is not None:
            self.logo_label.pack_forget()
            self.logo_label.destroy()
            self.logo_label = None
        self._logo_img = None

        if not self.logo_path or not Path(self.logo_path).exists():
            return

        try:
            img = Image.open(self.logo_path).convert("RGBA")

            # Window / taskbar icon
            icon = img.copy()
            icon.thumbnail((256, 256), Image.Resampling.LANCZOS)
            self._icon_img = ImageTk.PhotoImage(icon)
            self.iconphoto(True, self._icon_img)

            # Windows: a real .ico gives the sharpest title-bar/taskbar icon.
            if sys.platform.startswith("win") and LOGO_ICO.exists() \
                    and str(self.logo_path) == str(DEFAULT_LOGO):
                try:
                    self.iconbitmap(default=str(LOGO_ICO))
                except Exception:
                    pass

            # Toolbar logo + app name (inserted at the left of the top bar)
            small = img.copy()
            small.thumbnail((34, 34), Image.Resampling.LANCZOS)
            self._logo_img = ImageTk.PhotoImage(small)
            self.logo_label = ttk.Label(
                self.top_bar,
                image=self._logo_img,
                text=f" {APP_NAME}",
                compound="left",
                style="Top.TLabel",
                font=(self.ui_family, 11, "bold"),
            )
            first = self.top_bar.winfo_children()[0] if self.top_bar.winfo_children() else None
            if first is not None and first is not self.logo_label:
                self.logo_label.pack(side="left", padx=(0, 12), before=first)
            else:
                self.logo_label.pack(side="left", padx=(0, 12))
        except Exception as e:
            messagebox.showwarning("Logo", f"Could not load logo:\n{e}")

    def change_logo(self):
        path = filedialog.askopenfilename(
            title="Choose logo image",
            filetypes=[
                ("Images", "*.png *.jpg *.jpeg *.bmp *.gif *.webp"),
                ("All files", "*.*"),
            ],
        )
        if not path:
            return
        self.logo_path = path
        self.save_settings()
        self.apply_logo()

    def remove_logo(self):
        self.logo_path = None
        self.save_settings()
        self.apply_logo()

    # ============================================================
    # UI
    # ============================================================

    def _build_menu(self):
        menubar = tk.Menu(self)

        file_menu = tk.Menu(menubar, tearoff=False)
        file_menu.add_command(label="New Project", command=self.new_project)
        file_menu.add_command(label="Open Video...", command=self.open_video)
        file_menu.add_command(label="Open Image Folder...", command=self.open_image_folder)
        file_menu.add_separator()
        file_menu.add_command(label="Load Project...", command=self.load_project)
        file_menu.add_command(label="Save Project", command=self.save_project)
        file_menu.add_command(label="Save Project As...", command=self.save_project_as)
        file_menu.add_separator()
        file_menu.add_command(label="Export YOLO...", command=self.export_yolo)
        file_menu.add_command(label="Export COCO...", command=self.export_coco)
        file_menu.add_command(label="Export MOT...", command=self.export_mot)
        file_menu.add_command(
            label="Export Annotated Video...",
            command=self.export_annotated_video,
            accelerator="Ctrl+E",
        )
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_close)
        menubar.add_cascade(label="File", menu=file_menu)

        annotation_menu = tk.Menu(menubar, tearoff=False)
        annotation_menu.add_command(label="Add Class", command=self.add_class)
        annotation_menu.add_command(label="Edit Classes", command=self.edit_classes)
        annotation_menu.add_command(label="Create Individual ID", command=self.create_identity)
        annotation_menu.add_command(label="Assign Selected Box", command=self.assign_selected_identity)
        annotation_menu.add_command(label="Track Forward (ID Locked)", command=self.propagate_identity)
        annotation_menu.add_command(label="Set Rotation...", command=self.set_rotation_dialog)
        annotation_menu.add_command(label="Reset Rotation", command=self.reset_rotation)
        annotation_menu.add_command(label="Copy Previous Frame", command=self.copy_previous)
        annotation_menu.add_command(label="Delete Selected", command=self.delete_selected)
        annotation_menu.add_command(label="Clear Frame", command=self.clear_frame)
        menubar.add_cascade(label="Annotation", menu=annotation_menu)

        ai_menu = tk.Menu(menubar, tearoff=False)
        ai_menu.add_command(label="Simple Motion Propagation", command=self.propagate_current_identity)
        ai_menu.add_command(label="OpenCV Auto-Track Selected", command=self.auto_track_selected)
        ai_menu.add_separator()
        ai_menu.add_command(label="AI Integration Guide", command=self.show_ai_guide)
        menubar.add_cascade(label="AI / Tracking", menu=ai_menu)

        view_menu = tk.Menu(menubar, tearoff=False)
        view_menu.add_command(label="Project Statistics", command=self.show_stats)
        view_menu.add_command(label="Keyboard Shortcuts", command=self.show_help)
        view_menu.add_separator()
        view_menu.add_command(label="Change Logo...", command=self.change_logo)
        view_menu.add_command(label="Remove Logo", command=self.remove_logo)
        menubar.add_cascade(label="View", menu=view_menu)

        help_menu = tk.Menu(menubar, tearoff=False)
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.config(menu=menubar)

    def _build_ui(self):
        top = ttk.Frame(self, padding=(10, 8), style="Top.TFrame")
        top.pack(fill="x")
        self.top_bar = top

        self.accent_strip = tk.Canvas(
            self, height=3, bd=0, highlightthickness=0, bg=THEME["bg"]
        )
        self.accent_strip.pack(fill="x")
        self.accent_strip.bind("<Configure>", self._draw_accent_strip)

        buttons = [
            ("New", self.new_project),
            ("Open Video", self.open_video),
            ("Open Images", self.open_image_folder),
            ("Save", self.save_project),
            ("Add Class", self.add_class),
            ("New ID", self.create_identity),
            ("Draw Box", self.start_draw),
            ("Track Forward", self.propagate_identity),
            ("Auto Track", self.auto_track_selected),
            ("Copy Prev", self.copy_previous),
            ("Delete", self.delete_selected),
            ("YOLO", self.export_yolo),
            ("COCO", self.export_coco),
            ("MOT", self.export_mot),
            ("Save Video", self.export_annotated_video),
        ]
        for txt, cmd in buttons:
            accent = txt in ("Save", "Save Video")
            ttk.Button(
                top, text=txt, command=cmd,
                style="Tool.Accent.TButton" if accent else "Tool.TButton",
            ).pack(side="left", padx=2)

        self.media_label = ttk.Label(top, text="No media", style="Top.TLabel")
        self.media_label.pack(side="right", padx=8)

        body = ttk.PanedWindow(self, orient="horizontal")
        body.pack(fill="both", expand=True, padx=6, pady=4)

        # ---------------- LEFT PANEL ----------------
        left = ttk.Frame(body, width=245)
        body.add(left, weight=0)

        ttk.Label(
            left, text="CLASSES",
            style="Header.TLabel"
        ).pack(anchor="w", padx=8, pady=(8, 3))

        class_frame = ttk.Frame(left)
        class_frame.pack(fill="x", padx=6)

        self.class_list = tk.Listbox(
            class_frame,
            height=8,
            exportselection=False
        )
        self.class_list.pack(fill="x")
        self.class_list.bind("<<ListboxSelect>>", self.on_class_select)

        class_buttons = ttk.Frame(left)
        class_buttons.pack(fill="x", padx=6, pady=4)
        ttk.Button(class_buttons, text="+ Add", command=self.add_class).pack(
            side="left", fill="x", expand=True, padx=2
        )
        ttk.Button(class_buttons, text="Edit", command=self.edit_classes).pack(
            side="left", fill="x", expand=True, padx=2
        )

        ttk.Separator(left).pack(fill="x", padx=6, pady=8)

        ttk.Label(
            left, text="INDIVIDUAL IDs",
            style="Header.TLabel"
        ).pack(anchor="w", padx=8, pady=(0, 3))

        self.identity_list = tk.Listbox(
            left,
            height=13,
            exportselection=False
        )
        self.identity_list.pack(fill="both", expand=True, padx=6)
        self.identity_list.bind("<<ListboxSelect>>", self.on_identity_select)

        id_buttons = ttk.Frame(left)
        id_buttons.pack(fill="x", padx=6, pady=4)
        ttk.Button(id_buttons, text="+ New ID", command=self.create_identity).pack(
            side="left", fill="x", expand=True, padx=2
        )
        ttk.Button(id_buttons, text="Assign", command=self.assign_selected_identity).pack(
            side="left", fill="x", expand=True, padx=2
        )

        ttk.Button(
            left,
            text="Identity Manager",
            command=self.identity_manager
        ).pack(fill="x", padx=6, pady=3)

        ttk.Separator(left).pack(fill="x", padx=6, pady=8)

        ttk.Label(
            left, text="CURRENT FRAME OBJECTS",
            style="Header.TLabel"
        ).pack(anchor="w", padx=8)

        self.object_list = tk.Listbox(
            left,
            height=10,
            exportselection=False
        )
        self.object_list.pack(fill="both", expand=True, padx=6, pady=4)
        self.object_list.bind("<<ListboxSelect>>", self.on_object_select)

        # ---------------- CENTER ----------------
        center = ttk.Frame(body)
        body.add(center, weight=1)

        self.canvas = tk.Canvas(
            center,
            background=THEME["backdrop_bottom"],
            cursor="crosshair"
        )
        self.canvas.pack(fill="both", expand=True)

        self.canvas.bind("<ButtonPress-1>", self.mouse_down)
        self.canvas.bind("<B1-Motion>", self.mouse_move)
        self.canvas.bind("<ButtonRelease-1>", self.mouse_up)
        self.canvas.bind("<Button-3>", self.right_click)
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        self._welcome_btns = [
            ttk.Button(self.canvas, text="Open Video",
                       style="Hero.Accent.TButton", command=self.open_video),
            ttk.Button(self.canvas, text="Open Image Folder",
                       style="Hero.TButton", command=self.open_image_folder),
        ]

        controls = ttk.Frame(center, padding=5)
        controls.pack(fill="x")

        ttk.Button(controls, text="◀", command=self.prev_frame).pack(side="left")
        ttk.Button(controls, text="▶", command=self.next_frame).pack(side="left", padx=2)
        ttk.Button(controls, text="▶ Play", command=self.toggle_play).pack(side="left", padx=4)

        ttk.Label(controls, text="Frame").pack(side="left", padx=(15, 3))

        self.frame_var = tk.StringVar(value="0")
        self.frame_entry = ttk.Entry(
            controls, textvariable=self.frame_var, width=8
        )
        self.frame_entry.pack(side="left")
        self.frame_entry.bind("<Return>", self.goto_frame)

        ttk.Button(controls, text="Go", command=self.goto_frame).pack(side="left", padx=3)

        self.frame_label = ttk.Label(controls, text="0 / 0")
        self.frame_label.pack(side="left", padx=10)

        ttk.Label(controls, text="Zoom").pack(side="left", padx=(20, 3))
        ttk.Button(controls, text="-", command=self.zoom_out).pack(side="left")
        ttk.Button(controls, text="Fit", command=self.redraw).pack(side="left", padx=2)
        ttk.Button(controls, text="+", command=self.zoom_in).pack(side="left")

        self.timeline = ttk.Scale(
            controls,
            from_=0,
            to=1,
            orient="horizontal",
            command=self.timeline_changed
        )
        self.timeline.pack(side="left", fill="x", expand=True, padx=10)

        self.time_label = ttk.Label(controls, text="00:00 / 00:00")
        self.time_label.pack(side="right")

        # ---------------- RIGHT PANEL ----------------
        right = ttk.Frame(body, width=270)
        body.add(right, weight=0)

        ttk.Label(
            right,
            text="SELECTED OBJECT",
            style="Header.TLabel"
        ).pack(anchor="w", padx=8, pady=(8, 8))

        form = ttk.Frame(right)
        form.pack(fill="x", padx=8)

        self.info_vars = {
            "class": tk.StringVar(value="-"),
            "individual": tk.StringVar(value="-"),
            "track": tk.StringVar(value="-"),
            "bbox": tk.StringVar(value="-"),
            "angle": tk.StringVar(value="0.0"),
            "visibility": tk.StringVar(value="1.0"),
            "occluded": tk.StringVar(value="False"),
            "confidence": tk.StringVar(value="1.0"),
        }

        for row, (label, var) in enumerate(self.info_vars.items()):
            ttk.Label(form, text=label.title()).grid(
                row=row, column=0, sticky="w", pady=3
            )
            ttk.Label(
                form, textvariable=var
            ).grid(row=row, column=1, sticky="w", padx=8)

        ttk.Separator(right).pack(fill="x", padx=8, pady=12)

        ttk.Button(
            right,
            text="Assign Selected → Active ID",
            command=self.assign_selected_identity
        ).pack(fill="x", padx=8, pady=3)

        ttk.Button(
            right,
            text="Create New ID + Assign",
            command=self.create_and_assign
        ).pack(fill="x", padx=8, pady=3)

        ttk.Button(
            right,
            text="Toggle Occlusion",
            command=self.toggle_occlusion
        ).pack(fill="x", padx=8, pady=3)

        rot_row = ttk.Frame(right)
        rot_row.pack(fill="x", padx=8, pady=3)
        ttk.Button(rot_row, text="⟲ 5°", width=6,
                   command=lambda: self.rotate_selected(-5)).pack(side="left", expand=True, fill="x")
        ttk.Button(rot_row, text="⟳ 5°", width=6,
                   command=lambda: self.rotate_selected(5)).pack(side="left", expand=True, fill="x", padx=2)
        ttk.Button(rot_row, text="Set…", width=6,
                   command=self.set_rotation_dialog).pack(side="left", expand=True, fill="x")
        ttk.Button(rot_row, text="Reset", width=6,
                   command=self.reset_rotation).pack(side="left", expand=True, fill="x", padx=(2, 0))

        ttk.Button(
            right,
            text="Delete Selected",
            command=self.delete_selected
        ).pack(fill="x", padx=8, pady=3)

        ttk.Button(
            right,
            text="Copy Previous Frame",
            command=self.copy_previous
        ).pack(fill="x", padx=8, pady=3)

        ttk.Button(
            right,
            text="Track Forward (ID Locked)",
            command=self.propagate_identity
        ).pack(fill="x", padx=8, pady=3)

        ttk.Separator(right).pack(fill="x", padx=8, pady=12)

        ttk.Label(
            right,
            text="PROJECT INFO",
            style="Header.TLabel"
        ).pack(anchor="w", padx=8)

        self.project_info = tk.StringVar(value="")
        ttk.Label(
            right,
            textvariable=self.project_info,
            justify="left",
            wraplength=245
        ).pack(anchor="w", padx=8, pady=4)

        self.status_var = tk.StringVar(value="Ready")
        ttk.Label(
            self,
            textvariable=self.status_var,
            style="Status.TLabel",
            anchor="w"
        ).pack(fill="x")

        self.refresh_class_list()
        self.refresh_identity_list()

    def _bind_keys(self):
        self.bind("<Left>", lambda e: self.prev_frame())
        self.bind("<Right>", lambda e: self.next_frame())
        self.bind("<space>", lambda e: self.toggle_play())
        self.bind("<Delete>", lambda e: self.delete_selected())
        self.bind("<BackSpace>", lambda e: self.delete_selected())
        self.bind("<s>", lambda e: self.save_project())
        self.bind("<S>", lambda e: self.save_project())
        self.bind("<c>", lambda e: self.copy_previous())
        self.bind("<C>", lambda e: self.copy_previous())
        self.bind("<x>", lambda e: self.clear_frame())
        self.bind("<X>", lambda e: self.clear_frame())
        self.bind("<Control-e>", lambda e: self.export_annotated_video())
        self.bind("<Control-E>", lambda e: self.export_annotated_video())

        # Rotation: [ / ] = 1 degree, { / } = 15 degrees, 0 = reset
        self.bind("<bracketleft>", lambda e: self.rotate_selected(-1))
        self.bind("<bracketright>", lambda e: self.rotate_selected(1))
        self.bind("<braceleft>", lambda e: self.rotate_selected(-15))
        self.bind("<braceright>", lambda e: self.rotate_selected(15))
        self.bind("<r>", lambda e: self.rotate_selected(5))
        self.bind("<R>", lambda e: self.rotate_selected(-5))

        for n in range(1, 10):
            self.bind(
                str(n),
                lambda e, x=n: self.keyboard_select_id(x)
            )

    # ============================================================
    # PROJECT / MEDIA
    # ============================================================

    def new_project(self):
        if self.total_frames and messagebox.askyesno(
            "New project",
            "Save the current project before creating a new one?"
        ):
            self.save_project()

        self.close_media()

        self.media_type = None
        self.video_path = None
        self.image_paths = []
        self.total_frames = 0
        self.frame_idx = 0
        self.fps = 25.0
        self.frame_bgr = None

        self.project_file = None
        self.project_dir = None
        self.project_name = "Untitled"

        self.classes = {0: {"name": "person"}}
        self.identities = {}
        self.annotations = {}
        self.next_individual_id = 1
        self.next_track_id = 1
        self.current_boxes = []
        self.selected_index = None

        self.refresh_class_list()
        self.refresh_identity_list()
        self.refresh_object_list()
        self.redraw()
        self.update_status()

    def open_video(self):
        path = filedialog.askopenfilename(
            title="Open Video",
            filetypes=[
                ("Video files", "*.mp4 *.avi *.mov *.mkv *.m4v"),
                ("All files", "*.*")
            ]
        )
        if not path:
            return

        self.close_media()

        self.video_path = path
        self.media_type = "video"

        self.cap = cv2.VideoCapture(path)
        if not self.cap.isOpened():
            messagebox.showerror("Error", "Could not open video.")
            return

        self.total_frames = int(
            self.cap.get(cv2.CAP_PROP_FRAME_COUNT)
        )
        self.fps = self.cap.get(cv2.CAP_PROP_FPS) or 25.0
        self.frame_idx = 0

        self.project_name = Path(path).stem
        self.project_dir = str(
            Path(path).parent / f"{Path(path).stem}_RahatLabelStudio"
        )
        Path(self.project_dir).mkdir(parents=True, exist_ok=True)

        self.media_label.config(text=Path(path).name)

        self.show_frame(0)

    def open_image_folder(self):
        folder = filedialog.askdirectory(
            title="Select image folder"
        )
        if not folder:
            return

        extensions = {
            ".jpg", ".jpeg", ".png", ".bmp",
            ".webp", ".tif", ".tiff"
        }

        paths = sorted(
            str(p)
            for p in Path(folder).iterdir()
            if p.suffix.lower() in extensions
        )

        if not paths:
            messagebox.showwarning(
                "No images",
                "No supported images were found."
            )
            return

        self.close_media()

        self.media_type = "images"
        self.image_paths = paths
        self.total_frames = len(paths)
        self.fps = 1.0
        self.frame_idx = 0

        self.project_name = Path(folder).name
        self.project_dir = str(
            Path(folder) / "RahatLabelStudio_Project"
        )
        Path(self.project_dir).mkdir(parents=True, exist_ok=True)

        self.media_label.config(
            text=f"{Path(folder).name} ({len(paths)} images)"
        )

        self.show_frame(0)

    def close_media(self):
        if self.cap is not None:
            self.cap.release()
        self.cap = None

    def read_frame(self, idx):
        if self.media_type == "video":
            if not self.cap:
                return None
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, idx)
            ok, frame = self.cap.read()
            return frame if ok else None

        if self.media_type == "images":
            if 0 <= idx < len(self.image_paths):
                return cv2.imread(self.image_paths[idx])

        return None

    def show_frame(self, idx):
        if self.total_frames <= 0:
            return

        idx = max(0, min(int(idx), self.total_frames - 1))
        self.commit_current()

        frame = self.read_frame(idx)
        if frame is None:
            return

        self.frame_idx = idx
        self.frame_bgr = frame

        self.current_boxes = [
            self.deep_copy_annotation(a)
            for a in self.annotations.get(idx, [])
        ]

        self.selected_index = None

        self.refresh_object_list()
        self.update_info_panel()
        self.redraw()
        self.update_status()

    # ============================================================
    # CLASS MANAGEMENT
    # ============================================================

    def refresh_class_list(self):
        self.class_list.delete(0, "end")

        for cid in sorted(self.classes):
            self.class_list.insert(
                "end",
                f"{cid}: {self.classes[cid]['name']}"
            )

        ids = sorted(self.classes)
        if self.active_class_id in ids:
            self.class_list.selection_set(
                ids.index(self.active_class_id)
            )

    def on_class_select(self, _event=None):
        sel = self.class_list.curselection()
        if not sel:
            return

        ids = sorted(self.classes)
        self.active_class_id = ids[sel[0]]
        self.update_status()

    def add_class(self):
        name = simpledialog.askstring(
            "Add class",
            "Class name:",
            parent=self
        )

        if not name:
            return

        name = name.strip()

        if any(
            c["name"].lower() == name.lower()
            for c in self.classes.values()
        ):
            messagebox.showwarning(
                "Duplicate class",
                "This class already exists."
            )
            return

        cid = max(self.classes.keys(), default=-1) + 1
        self.classes[cid] = {"name": name}
        self.active_class_id = cid

        self.refresh_class_list()
        self.update_status()

    def edit_classes(self):
        messagebox.showinfo(
            "Classes",
            "\n".join(
                f"{cid}: {v['name']}"
                for cid, v in sorted(self.classes.items())
            )
        )

    # ============================================================
    # IDENTITY MANAGEMENT
    # ============================================================

    def create_identity(self):
        iid = self.next_individual_id
        self.next_individual_id += 1

        self.identities[iid] = {
            "individual_id": iid,
            "class_id": self.active_class_id,
            "name": f"ID_{iid:03d}",
            "notes": "",
        }

        self.active_individual_id = iid

        self.refresh_identity_list()
        self.update_status()

    def create_and_assign(self):
        self.create_identity()

        if self.selected_index is not None:
            self.assign_selected_identity()

    def refresh_identity_list(self):
        self.identity_list.delete(0, "end")

        for iid in sorted(self.identities):
            item = self.identities[iid]
            cid = item["class_id"]
            cname = self.classes.get(cid, {}).get("name", "unknown")

            self.identity_list.insert(
                "end",
                f"ID {iid:03d} | {cname}"
            )

        if self.active_individual_id in self.identities:
            ids = sorted(self.identities)
            pos = ids.index(self.active_individual_id)
            self.identity_list.selection_set(pos)

    def on_identity_select(self, _event=None):
        sel = self.identity_list.curselection()

        if not sel:
            return

        ids = sorted(self.identities)
        self.active_individual_id = ids[sel[0]]

        item = self.identities[self.active_individual_id]
        self.active_class_id = item["class_id"]

        self.refresh_class_list()
        self.update_status()

    def keyboard_select_id(self, n):
        # If ID exists, select it.
        if n in self.identities:
            self.active_individual_id = n
            self.active_class_id = self.identities[n]["class_id"]
            self.refresh_identity_list()
            self.refresh_class_list()
            self.update_status()

    def identity_manager(self):
        if not self.identities:
            messagebox.showinfo(
                "Identity Manager",
                "No individual IDs created yet."
            )
            return

        rows = []

        for iid in sorted(self.identities):
            item = self.identities[iid]
            cname = self.classes.get(
                item["class_id"], {}
            ).get("name", "unknown")

            count = sum(
                1
                for anns in self.annotations.values()
                for a in anns
                if a["individual_id"] == iid
            )

            rows.append(
                f"ID {iid:03d} | {cname} | annotations={count}"
            )

        messagebox.showinfo(
            "Identity Manager",
            "\n".join(rows)
        )

    # ============================================================
    # ANNOTATION
    # ============================================================

    def start_draw(self):
        self.canvas.config(cursor="crosshair")
        self.status_var.set(
            f"Draw box: class={self.classes[self.active_class_id]['name']} "
            f"ID={self.active_individual_id} | Select a box, then drag a corner to resize"
        )

    def mouse_down(self, event):
        if self.frame_bgr is None:
            return

        fx, fy = self.canvas_to_frame(event.x, event.y)

        # Rotation handle of the currently selected box has priority.
        if (
            self.selected_index is not None
            and self.selected_index < len(self.current_boxes)
        ):
            sel = self.current_boxes[self.selected_index]
            if self.hit_test_rotate_handle(fx, fy, sel["bbox"], sel.get("angle", 0.0)):
                self.drag_mode = "rotate"
                self.drag_box_index = self.selected_index
                self.original_bbox = list(sel["bbox"])
                return

        # First look for an existing object. Corners are resize handles;
        # clicking inside the box moves the whole box.
        for i in range(len(self.current_boxes) - 1, -1, -1):
            x1, y1, x2, y2 = self.current_boxes[i]["bbox"]
            angle = self.current_boxes[i].get("angle", 0.0)
            handle = self.hit_test_resize_handle(fx, fy, self.current_boxes[i]["bbox"], angle)
            if handle is not None:
                self.selected_index = i
                self.drag_mode = "resize"
                self.drag_box_index = i
                self.resize_handle = handle
                self.drag_start_frame = (fx, fy)
                self.original_bbox = list(self.current_boxes[i]["bbox"])
                self.refresh_object_list()
                self.update_info_panel()
                self.redraw()
                return

            if self.point_in_box(fx, fy, self.current_boxes[i]["bbox"], angle):
                self.selected_index = i
                self.drag_mode = "move"
                self.drag_box_index = i
                self.drag_start_frame = (fx, fy)
                self.original_bbox = list(self.current_boxes[i]["bbox"])
                self.refresh_object_list()
                self.update_info_panel()
                self.redraw()
                return

        self.drag_mode = "draw"
        self.drag_start_canvas = (event.x, event.y)

    def mouse_move(self, event):
        if self.drag_mode == "draw":
            self.drag_current_canvas = (event.x, event.y)
            self.redraw()

        elif (
            self.drag_mode == "resize"
            and self.drag_box_index is not None
            and self.resize_handle is not None
        ):
            fx, fy = self.canvas_to_frame(event.x, event.y)
            x1, y1, x2, y2 = self.original_bbox
            angle = self.current_boxes[self.drag_box_index].get("angle", 0.0)
            min_size = 5.0

            # Rotation-aware resize: the opposite corner stays fixed in the
            # image, the dragged corner follows the mouse.
            ocx, ocy = (x1 + x2) / 2.0, (y1 + y2) / 2.0
            corners = {
                "tl": (x1, y1), "tr": (x2, y1),
                "br": (x2, y2), "bl": (x1, y2),
            }
            opposite = {"tl": "br", "tr": "bl", "br": "tl", "bl": "tr"}
            ox_, oy_ = corners[opposite[self.resize_handle]]
            opp = self.rot_pt(ox_, oy_, ocx, ocy, angle)

            ncx, ncy = (opp[0] + fx) / 2.0, (opp[1] + fy) / 2.0
            lx, ly = self.rot_pt(fx, fy, ncx, ncy, -angle)
            hw = max(min_size / 2.0, abs(lx - ncx))
            hh = max(min_size / 2.0, abs(ly - ncy))

            self.current_boxes[self.drag_box_index]["bbox"] = [
                ncx - hw, ncy - hh, ncx + hw, ncy + hh
            ]
            self.redraw()
            self.update_info_panel()

        elif (
            self.drag_mode == "rotate"
            and self.drag_box_index is not None
        ):
            fx, fy = self.canvas_to_frame(event.x, event.y)
            x1, y1, x2, y2 = self.current_boxes[self.drag_box_index]["bbox"]
            cx, cy = (x1 + x2) / 2.0, (y1 + y2) / 2.0
            angle = math.degrees(math.atan2(fx - cx, -(fy - cy)))
            if event.state & 0x0001:  # Shift = snap to 15 degrees
                angle = round(angle / 15.0) * 15.0
            self.current_boxes[self.drag_box_index]["angle"] = self.norm_angle(angle)
            self.redraw()
            self.update_info_panel()

        elif (
            self.drag_mode == "move"
            and self.drag_box_index is not None
        ):
            fx, fy = self.canvas_to_frame(
                event.x, event.y
            )

            sx, sy = self.drag_start_frame
            dx, dy = fx - sx, fy - sy

            x1, y1, x2, y2 = self.original_bbox

            h, w = self.frame_bgr.shape[:2]

            nx1 = max(0, min(w, x1 + dx))
            nx2 = max(0, min(w, x2 + dx))
            ny1 = max(0, min(h, y1 + dy))
            ny2 = max(0, min(h, y2 + dy))

            self.current_boxes[
                self.drag_box_index
            ]["bbox"] = [
                nx1, ny1, nx2, ny2
            ]

            self.redraw()
            self.update_info_panel()

    def mouse_up(self, event):
        if self.drag_mode == "draw":
            x1, y1 = self.canvas_to_frame(
                *self.drag_start_canvas
            )
            x2, y2 = self.canvas_to_frame(
                event.x, event.y
            )

            x1, x2 = sorted([x1, x2])
            y1, y2 = sorted([y1, y2])

            if x2 - x1 >= 5 and y2 - y1 >= 5:
                h, w = self.frame_bgr.shape[:2]

                annotation = {
                    "class_id": self.active_class_id,
                    "individual_id": self.active_individual_id,
                    "track_id": self.next_track_id,
                    "bbox": [
                        max(0, x1),
                        max(0, y1),
                        min(w, x2),
                        min(h, y2)
                    ],
                    "angle": 0.0,
                    "occluded": False,
                    "visibility": 1.0,
                    "confidence": 1.0
                }

                self.next_track_id += 1

                self.current_boxes.append(annotation)
                self.selected_index = (
                    len(self.current_boxes) - 1
                )

                # Make sure identity exists.
                if self.active_individual_id not in self.identities:
                    self.identities[
                        self.active_individual_id
                    ] = {
                        "individual_id":
                            self.active_individual_id,
                        "class_id":
                            self.active_class_id,
                        "name":
                            f"ID_{self.active_individual_id:03d}",
                        "notes": ""
                    }

                self.commit_current()
                self.refresh_identity_list()
                self.refresh_object_list()

        elif self.drag_mode == "move":
            self.commit_current()

        if self.drag_mode in ("move", "resize", "rotate"):
            self.commit_current()

        self.drag_mode = None
        self.drag_box_index = None
        self.resize_handle = None
        self.original_bbox = None

        self.redraw()

    # ---------------- Rotation geometry ----------------

    @staticmethod
    def norm_angle(a):
        """Normalize to (-180, 180]."""
        a = (a + 180.0) % 360.0 - 180.0
        return 180.0 if a == -180.0 else a

    @staticmethod
    def rot_pt(px, py, cx, cy, angle_deg):
        """Rotate point around (cx, cy) by angle (degrees, clockwise on screen)."""
        r = math.radians(angle_deg)
        c, s = math.cos(r), math.sin(r)
        dx, dy = px - cx, py - cy
        return (cx + dx * c - dy * s, cy + dx * s + dy * c)

    def box_corners(self, bbox, angle=0.0):
        """Four corners (tl, tr, br, bl) of the rotated box in image coords."""
        x1, y1, x2, y2 = bbox
        cx, cy = (x1 + x2) / 2.0, (y1 + y2) / 2.0
        pts = [(x1, y1), (x2, y1), (x2, y2), (x1, y2)]
        return [self.rot_pt(px, py, cx, cy, angle) for px, py in pts]

    def box_envelope(self, bbox, angle=0.0):
        """Axis-aligned bounding rectangle around the rotated box."""
        pts = self.box_corners(bbox, angle)
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        return [min(xs), min(ys), max(xs), max(ys)]

    def point_in_box(self, fx, fy, bbox, angle=0.0):
        x1, y1, x2, y2 = bbox
        cx, cy = (x1 + x2) / 2.0, (y1 + y2) / 2.0
        lx, ly = self.rot_pt(fx, fy, cx, cy, -angle)
        return x1 <= lx <= x2 and y1 <= ly <= y2

    def rotate_handle_pos(self, bbox, angle=0.0):
        x1, y1, x2, y2 = bbox
        cx = (x1 + x2) / 2.0
        cy = (y1 + y2) / 2.0
        dist = 28.0 / max(self.scale, 0.01)
        return self.rot_pt(cx, y1 - dist, cx, cy, angle)

    def hit_test_rotate_handle(self, fx, fy, bbox, angle=0.0):
        hx, hy = self.rotate_handle_pos(bbox, angle)
        tol = max(6.0, 10.0 / max(self.scale, 0.01))
        return abs(fx - hx) <= tol and abs(fy - hy) <= tol

    def rotate_selected(self, delta):
        if self.selected_index is None or self.selected_index >= len(self.current_boxes):
            return
        obj = self.current_boxes[self.selected_index]
        obj["angle"] = self.norm_angle(obj.get("angle", 0.0) + delta)
        self.commit_current()
        self.update_info_panel()
        self.redraw()

    def reset_rotation(self):
        if self.selected_index is None or self.selected_index >= len(self.current_boxes):
            return
        self.current_boxes[self.selected_index]["angle"] = 0.0
        self.commit_current()
        self.update_info_panel()
        self.redraw()

    def set_rotation_dialog(self):
        if self.selected_index is None or self.selected_index >= len(self.current_boxes):
            messagebox.showinfo("Rotate", "Select a box first.")
            return
        obj = self.current_boxes[self.selected_index]
        value = simpledialog.askfloat(
            "Set rotation",
            "Angle in degrees (clockwise, -180 to 180):",
            initialvalue=obj.get("angle", 0.0),
            minvalue=-360, maxvalue=360, parent=self,
        )
        if value is None:
            return
        obj["angle"] = self.norm_angle(value)
        self.commit_current()
        self.update_info_panel()
        self.redraw()

    def hit_test_resize_handle(self, fx, fy, bbox, angle=0.0):
        """Return corner handle name if cursor is close to a selected box corner."""
        x1, y1, x2, y2 = bbox
        # tolerance is in image pixels and scales with zoom
        tol = max(6.0, 10.0 / max(self.scale, 0.01))
        corners = dict(zip(("tl", "tr", "br", "bl"), self.box_corners(bbox, angle)))
        for name, (cx, cy) in corners.items():
            if abs(fx - cx) <= tol and abs(fy - cy) <= tol:
                return name
        return None

    def right_click(self, event):
        fx, fy = self.canvas_to_frame(
            event.x, event.y
        )

        for i in range(len(self.current_boxes) - 1, -1, -1):
            x1, y1, x2, y2 = (
                self.current_boxes[i]["bbox"]
            )

            if self.point_in_box(fx, fy, self.current_boxes[i]["bbox"], self.current_boxes[i].get("angle", 0.0)):
                self.selected_index = i
                self.refresh_object_list()
                self.update_info_panel()
                self.redraw()
                return

    def assign_selected_identity(self):
        if self.selected_index is None:
            messagebox.showinfo(
                "Assign",
                "Select an object first."
            )
            return

        if self.active_individual_id not in self.identities:
            self.create_identity()

        obj = self.current_boxes[
            self.selected_index
        ]

        obj["individual_id"] = (
            self.active_individual_id
        )
        obj["class_id"] = self.active_class_id

        self.commit_current()
        self.refresh_object_list()
        self.refresh_identity_list()
        self.update_info_panel()
        self.redraw()

    def toggle_occlusion(self):
        if self.selected_index is None:
            return

        obj = self.current_boxes[
            self.selected_index
        ]

        obj["occluded"] = not obj.get(
            "occluded", False
        )

        self.commit_current()
        self.update_info_panel()
        self.redraw()

    def delete_selected(self):
        if self.selected_index is None:
            return

        if 0 <= self.selected_index < len(
            self.current_boxes
        ):
            del self.current_boxes[
                self.selected_index
            ]

        self.selected_index = None
        self.commit_current()
        self.refresh_object_list()
        self.update_info_panel()
        self.redraw()

    def clear_frame(self):
        if not self.current_boxes:
            return

        if not messagebox.askyesno(
            "Clear frame",
            "Delete all annotations on this frame?"
        ):
            return

        self.current_boxes = []
        self.selected_index = None
        self.commit_current()
        self.refresh_object_list()
        self.update_info_panel()
        self.redraw()

    def copy_previous(self):
        if self.frame_idx <= 0:
            return

        previous = self.annotations.get(
            self.frame_idx - 1, []
        )

        if not previous:
            messagebox.showinfo(
                "Copy Previous",
                "Previous frame has no annotations."
            )
            return

        self.current_boxes = [
            self.deep_copy_annotation(a)
            for a in previous
        ]

        self.commit_current()
        self.refresh_object_list()
        self.update_info_panel()
        self.redraw()

    # ============================================================
    # ID PROPAGATION
    # ============================================================

    def propagate_identity(self):
        """Track forward with persistent ID and explicit occlusion handling.

        Rules:
        1. The manually assigned Individual ID is never changed automatically.
        2. If the person becomes occluded / tracking confidence becomes unsafe,
           the bounding box is REMOVED for that frame instead of being frozen
           or transferred to another person.
        3. The identity itself remains available for later manual re-labeling.
        4. When the person becomes visible again, a later manual box can simply
           be assigned to the same existing Individual ID.
        """
        if self.selected_index is None:
            messagebox.showinfo("Track Forward", "Select the person's bounding box first.")
            return

        if self.frame_bgr is None or self.total_frames <= 1:
            return

        source = self.current_boxes[self.selected_index]
        iid = int(source["individual_id"])
        class_id = int(source["class_id"])
        start = self.frame_idx

        end = simpledialog.askinteger(
            "Track Forward",
            f"Track locked ID {iid} until frame number:",
            initialvalue=min(self.total_frames - 1, start + 100),
            minvalue=start,
            maxvalue=max(0, self.total_frames - 1),
            parent=self,
        )
        if end is None or end <= start:
            return

        reference_frame = self.frame_bgr.copy()
        reference_box = list(source["bbox"])
        reference_hist = self.compute_hsv_histogram(reference_frame, reference_box)
        template = self.crop_box(reference_frame, reference_box)
        previous_box = list(reference_box)

        tracker = self.create_tracker()
        if tracker is not None:
            x1, y1, x2, y2 = map(int, reference_box)
            try:
                tracker.init(reference_frame, (x1, y1, max(2, x2-x1), max(2, y2-y1)))
            except Exception:
                tracker = None

        accepted = 0
        lost_frames = 0
        was_lost = False
        self.propagating = True

        try:
            for idx in range(start + 1, end + 1):
                frame = self.read_frame(idx)
                if frame is None:
                    break

                candidate = None

                # Tracker prediction.
                if tracker is not None:
                    try:
                        ok, rect = tracker.update(frame)
                        if ok:
                            rx, ry, rw, rh = rect
                            if rw >= 4 and rh >= 4:
                                candidate = [
                                    float(rx), float(ry),
                                    float(rx + rw), float(ry + rh)
                                ]
                    except Exception:
                        candidate = None

                # Local refinement is attempted only around a real prediction.
                if candidate is not None:
                    refined = self.refine_box_with_template(frame, candidate, template)
                    if refined is not None:
                        candidate = refined

                score = 0.0
                if candidate is not None:
                    score, _details = self.validate_tracking_candidate(
                        frame, candidate, previous_box, reference_hist
                    )

                # IMPORTANT: no frozen box during occlusion.
                # The ID remains alive in self.identities, but this frame contains
                # no bounding-box annotation for that ID.
                if candidate is None or score < 0.52:
                    lost_frames += 1
                    was_lost = True

                    self.annotations[idx] = [
                        self.deep_copy_annotation(a)
                        for a in self.annotations.get(idx, [])
                        if int(a.get("individual_id", -1)) != iid
                    ]

                    # Do not let a stale tracker box influence later frames.
                    if lost_frames >= 1:
                        tracker = None

                    continue

                # Valid visible detection/tracking result.
                lost_frames = 0
                accepted += 1

                ann = self.deep_copy_annotation(source)
                ann["individual_id"] = iid
                ann["class_id"] = class_id
                ann["bbox"] = candidate
                ann["confidence"] = float(score)
                ann["track_id"] = int(source.get("track_id", 0))
                ann["occluded"] = False
                ann["visibility"] = 1.0

                frame_annotations = [
                    self.deep_copy_annotation(a)
                    for a in self.annotations.get(idx, [])
                    if int(a.get("individual_id", -1)) != iid
                ]
                frame_annotations.append(ann)
                self.annotations[idx] = frame_annotations

                previous_box = list(candidate)

                new_crop = self.crop_box(frame, candidate)
                if new_crop is not None and new_crop.size > 20:
                    template = cv2.addWeighted(template, 0.85, new_crop, 0.15, 0)

                # If the person reappears, a tracker can be re-created from the
                # newly validated box. This preserves the same Individual ID.
                if was_lost:
                    tracker = self.create_tracker()
                    if tracker is not None:
                        bx1, by1, bx2, by2 = map(int, candidate)
                        try:
                            tracker.init(
                                frame,
                                (bx1, by1, max(2, bx2-bx1), max(2, by2-by1))
                            )
                        except Exception:
                            tracker = None
                    was_lost = False

            self.commit_current()
        finally:
            self.propagating = False

        self.show_frame(start)
        messagebox.showinfo(
            "Track Forward complete",
            f"Locked Individual ID: {iid}\n\n"
            f"Visible/tracked frames: {accepted}\n"
            f"Occluded/lost frames: {lost_frames}\n\n"
            "During occlusion the bounding box is removed, not frozen.\n"
            "The Individual ID remains unchanged.\n\n"
            "When the person becomes visible again, draw a new box and\n"
            "assign the existing ID to continue the same identity."
        )

    def recover_identity_manual(self):
        """Helper action: select an existing ID, draw a new box, then assign it."""
        if self.active_individual_id not in self.identities:
            messagebox.showinfo("Identity Recovery", "Create/select the existing Individual ID first.")
            return
        self.start_draw()
        self.status_var.set(
            f"Recovery mode: draw the person again → assign existing ID {self.active_individual_id}"
        )

    def crop_box(self, frame, box, pad=0):
        if frame is None or box is None:
            return None
        h, w = frame.shape[:2]
        x1, y1, x2, y2 = map(int, box)
        x1 = max(0, x1-pad); y1 = max(0, y1-pad)
        x2 = min(w, x2+pad); y2 = min(h, y2+pad)
        if x2 <= x1 or y2 <= y1:
            return None
        return frame[y1:y2, x1:x2].copy()

    def compute_hsv_histogram(self, frame, box):
        crop = self.crop_box(frame, box)
        if crop is None or crop.size == 0:
            return None
        hsv = cv2.cvtColor(crop, cv2.COLOR_BGR2HSV)
        hist = cv2.calcHist([hsv], [0, 1], None, [24, 16], [0, 180, 0, 256])
        cv2.normalize(hist, hist)
        return hist

    def histogram_similarity(self, h1, h2):
        if h1 is None or h2 is None:
            return 0.0
        value = cv2.compareHist(h1, h2, cv2.HISTCMP_CORREL)
        return float(max(0.0, min(1.0, (value + 1.0) / 2.0)))

    def refine_box_with_template(self, frame, box, template):
        if template is None or template.size == 0:
            return box
        h, w = frame.shape[:2]
        x1, y1, x2, y2 = map(int, box)
        bw, bh = max(4, x2-x1), max(4, y2-y1)
        cx, cy = (x1+x2)//2, (y1+y2)//2
        margin_x, margin_y = max(30, int(bw*0.8)), max(30, int(bh*0.8))
        sx1, sy1 = max(0, cx-margin_x), max(0, cy-margin_y)
        sx2, sy2 = min(w, cx+margin_x), min(h, cy+margin_y)
        search = frame[sy1:sy2, sx1:sx2]
        if search.shape[0] < template.shape[0] or search.shape[1] < template.shape[1]:
            return box
        gray_s = cv2.cvtColor(search, cv2.COLOR_BGR2GRAY)
        gray_t = cv2.cvtColor(template, cv2.COLOR_BGR2GRAY)
        result = cv2.matchTemplate(gray_s, gray_t, cv2.TM_CCOEFF_NORMED)
        _, max_val, _, max_loc = cv2.minMaxLoc(result)
        if max_val < 0.35:
            return box
        tx, ty = max_loc
        return [float(sx1+tx), float(sy1+ty), float(sx1+tx+template.shape[1]), float(sy1+ty+template.shape[0])]

    def validate_tracking_candidate(self, frame, candidate, previous_box, reference_hist):
        h, w = frame.shape[:2]
        x1, y1, x2, y2 = candidate
        bw, bh = max(2.0, x2-x1), max(2.0, y2-y1)
        px1, py1, px2, py2 = previous_box
        pbw, pbh = max(2.0, px2-px1), max(2.0, py2-py1)
        pcx, pcy = (px1+px2)/2.0, (py1+py2)/2.0
        ccx, ccy = (x1+x2)/2.0, (y1+y2)/2.0
        max_move = max(40.0, 1.25 * max(pbw, pbh))
        distance = ((ccx-pcx)**2 + (ccy-pcy)**2) ** 0.5
        motion = max(0.0, min(1.0, 1.0 - distance/max_move))
        size = max(0.0, min(1.0, min(bw/pbw, pbw/bw) * min(bh/pbh, pbh/bh)))
        appearance = self.histogram_similarity(reference_hist, self.compute_hsv_histogram(frame, candidate))
        inside = 1.0 if (x2 > 0 and y2 > 0 and x1 < w and y1 < h) else 0.0
        score = 0.45*appearance + 0.35*motion + 0.15*size + 0.05*inside
        return float(score), {"appearance": appearance, "motion": motion, "size": size}

    def propagate_current_identity(self):
        self.propagate_identity()

    def create_tracker(self):
        candidates = []

        # Different OpenCV versions expose trackers differently.
        for name in [
            "TrackerCSRT_create",
            "TrackerKCF_create",
            "TrackerMIL_create"
        ]:
            fn = getattr(cv2, name, None)
            if fn:
                candidates.append(fn)

        legacy = getattr(cv2, "legacy", None)

        if legacy:
            for name in [
                "TrackerCSRT_create",
                "TrackerKCF_create",
                "TrackerMIL_create"
            ]:
                fn = getattr(legacy, name, None)
                if fn:
                    candidates.append(fn)

        for fn in candidates:
            try:
                return fn()
            except Exception:
                pass

        return None

    def auto_track_selected(self):
        self.propagate_identity()

    # ============================================================
    # NAVIGATION
    # ============================================================

    def prev_frame(self):
        if self.total_frames:
            self.show_frame(
                self.frame_idx - 1
            )

    def next_frame(self):
        if self.total_frames:
            self.show_frame(
                self.frame_idx + 1
            )

    def goto_frame(self, _event=None):
        if not self.total_frames:
            return

        try:
            value = int(
                self.frame_var.get()
            ) - 1
        except ValueError:
            return

        self.show_frame(value)

    def toggle_play(self):
        if not self.total_frames:
            return

        self.playing = not self.playing

        if self.playing:
            self.play_step()

    def play_step(self):
        if not self.playing:
            return

        if self.frame_idx >= (
            self.total_frames - 1
        ):
            self.playing = False
            return

        self.show_frame(
            self.frame_idx + 1
        )

        delay = max(
            1,
            int(
                1000 /
                max(self.fps, 1)
            )
        )

        self.after(
            delay,
            self.play_step
        )

    def timeline_changed(self, value):
        if not self.total_frames:
            return

        try:
            idx = int(float(value))
        except ValueError:
            return

        if idx != self.frame_idx:
            self.show_frame(idx)

    # ============================================================
    # DRAWING
    # ============================================================

    def redraw(self):
        if self.frame_bgr is None:
            self.canvas.delete("all")
            self._draw_welcome()
            return

        h, w = self.frame_bgr.shape[:2]

        cw = max(
            1,
            self.canvas.winfo_width()
        )
        ch = max(
            1,
            self.canvas.winfo_height()
        )

        fit_scale = min(
            cw / w,
            ch / h
        )

        scale = fit_scale
        self.scale = scale

        dw = int(w * scale)
        dh = int(h * scale)

        ox = int((cw - dw) / 2)
        oy = int((ch - dh) / 2)

        self.offset = (ox, oy)

        rgb = cv2.cvtColor(
            self.frame_bgr,
            cv2.COLOR_BGR2RGB
        )

        image = Image.fromarray(
            rgb
        ).resize(
            (dw, dh),
            Image.Resampling.LANCZOS
        )

        draw = ImageDraw.Draw(image)

        for i, obj in enumerate(
            self.current_boxes
        ):
            x1, y1, x2, y2 = obj["bbox"]

            X1 = int(x1 * scale)
            Y1 = int(y1 * scale)
            X2 = int(x2 * scale)
            Y2 = int(y2 * scale)

            iid = int(
                obj["individual_id"]
            )

            color = self.id_colors[
                (iid - 1) %
                len(self.id_colors)
            ]

            width = (
                4
                if i == self.selected_index
                else 2
            )

            if obj.get("occluded", False):
                width = max(
                    1,
                    width - 1
                )

            angle = obj.get("angle", 0.0)
            corners = [
                (px * scale, py * scale)
                for px, py in self.box_corners(obj["bbox"], angle)
            ]
            draw.line(corners + [corners[0]], fill=color, width=width, joint="curve")
            X1, Y1 = int(corners[0][0]), int(corners[0][1])

            # Show resize + rotation handles on the selected box only.
            if i == self.selected_index:
                hs = 5
                for hx, hy in corners:
                    draw.rectangle([hx-hs, hy-hs, hx+hs, hy+hs], fill=color, outline="white", width=1)

                # Rotation handle: circle on a stalk above the top edge.
                top_mid = (
                    (corners[0][0] + corners[1][0]) / 2.0,
                    (corners[0][1] + corners[1][1]) / 2.0,
                )
                rhx, rhy = self.rotate_handle_pos(obj["bbox"], angle)
                rhx, rhy = rhx * scale, rhy * scale
                draw.line([top_mid, (rhx, rhy)], fill=color, width=2)
                draw.ellipse([rhx-7, rhy-7, rhx+7, rhy+7], fill="white", outline=color, width=3)

            cname = self.classes.get(
                obj["class_id"],
                {"name": "unknown"}
            )["name"]

            label = (
                f"ID {iid} | {cname}"
            )

            try:
                tb = draw.textbbox(
                    (X1, Y1),
                    label
                )
                draw.rectangle(
                    tb,
                    fill=color
                )
                draw.text(
                    (X1 + 2, Y1 + 1),
                    label,
                    fill="white"
                )
            except Exception:
                pass

        # Current drawing rectangle.
        if (
            self.drag_mode == "draw"
            and hasattr(
                self,
                "drag_current_canvas"
            )
        ):
            x1, y1 = (
                self.drag_start_canvas
            )
            x2, y2 = (
                self.drag_current_canvas
            )

            self.canvas.delete(
                "draw_temp"
            )

            self.canvas.create_rectangle(
                x1, y1, x2, y2,
                outline="white",
                width=2,
                dash=(5, 3),
                tags="draw_temp"
            )

        self.photo = ImageTk.PhotoImage(
            image
        )

        self.canvas.delete(
            "all"
        )

        self._draw_canvas_backdrop(cw, ch)

        # soft drop-shadow + thin accent border around the frame
        for pad, col in ((12, "#080b17"), (8, "#0a0e1d"), (4, "#0f1429")):
            self.canvas.create_rectangle(
                ox - pad, oy - pad + 3, ox + dw + pad, oy + dh + pad + 3,
                fill=col, outline=""
            )

        self.canvas.create_image(
            ox,
            oy,
            anchor="nw",
            image=self.photo
        )

        self.canvas.create_rectangle(
            ox - 1, oy - 1, ox + dw, oy + dh,
            outline=THEME["border"], width=1
        )

        # Redraw temporary rectangle over image.
        if (
            self.drag_mode == "draw"
            and hasattr(
                self,
                "drag_current_canvas"
            )
        ):
            x1, y1 = (
                self.drag_start_canvas
            )
            x2, y2 = (
                self.drag_current_canvas
            )

            self.canvas.create_rectangle(
                x1, y1, x2, y2,
                outline="white",
                width=2,
                dash=(5, 3)
            )

    def canvas_to_frame(self, x, y):
        ox, oy = self.offset

        return (
            (x - ox) / self.scale,
            (y - oy) / self.scale
        )

    def zoom_in(self):
        # Kept simple: fit-to-window redraw.
        self.redraw()

    def zoom_out(self):
        self.redraw()

    # ============================================================
    # OBJECT LIST / INFO
    # ============================================================

    def refresh_object_list(self):
        self.object_list.delete(
            0, "end"
        )

        for i, obj in enumerate(
            self.current_boxes
        ):
            cid = obj["class_id"]
            iid = obj["individual_id"]

            cname = self.classes.get(
                cid,
                {"name": "unknown"}
            )["name"]

            self.object_list.insert(
                "end",
                f"{i+1}. ID {iid:03d} | {cname}"
            )

        if (
            self.selected_index is not None
            and self.selected_index <
            len(self.current_boxes)
        ):
            self.object_list.selection_set(
                self.selected_index
            )

        self.update_info_panel()

    def on_object_select(self, _event=None):
        sel = self.object_list.curselection()

        if not sel:
            return

        self.selected_index = sel[0]

        self.update_info_panel()
        self.redraw()

    def update_info_panel(self):
        if (
            self.selected_index is None
            or self.selected_index >=
            len(self.current_boxes)
        ):
            for v in self.info_vars.values():
                v.set("-")
            return

        obj = self.current_boxes[
            self.selected_index
        ]

        cname = self.classes.get(
            obj["class_id"],
            {"name": "unknown"}
        )["name"]

        x1, y1, x2, y2 = obj["bbox"]

        self.info_vars[
            "class"
        ].set(
            f"{cname} ({obj['class_id']})"
        )

        self.info_vars[
            "individual"
        ].set(
            str(obj["individual_id"])
        )

        self.info_vars[
            "track"
        ].set(
            str(obj.get("track_id", "-"))
        )

        self.info_vars[
            "bbox"
        ].set(
            f"{int(x1)}, {int(y1)}, "
            f"{int(x2)}, {int(y2)}"
        )

        self.info_vars["angle"].set(f"{obj.get('angle', 0.0):.1f}°")

        self.info_vars[
            "visibility"
        ].set(
            f"{obj.get('visibility', 1.0):.2f}"
        )

        self.info_vars[
            "occluded"
        ].set(
            str(
                obj.get(
                    "occluded",
                    False
                )
            )
        )

        self.info_vars[
            "confidence"
        ].set(
            f"{obj.get('confidence', 1.0):.2f}"
        )

    # ============================================================
    # PROJECT SAVE / LOAD
    # ============================================================

    def commit_current(self):
        if self.total_frames <= 0:
            return

        self.annotations[
            self.frame_idx
        ] = [
            self.deep_copy_annotation(a)
            for a in self.current_boxes
        ]

    @staticmethod
    def deep_copy_annotation(a):
        return {
            "class_id": int(
                a.get("class_id", 0)
            ),
            "individual_id": int(
                a.get("individual_id", 1)
            ),
            "track_id": int(
                a.get("track_id", 0)
            ),
            "bbox": [
                float(x)
                for x in a.get(
                    "bbox",
                    [0, 0, 0, 0]
                )
            ],
            "angle": float(a.get("angle", 0.0)),
            "occluded": bool(
                a.get(
                    "occluded",
                    False
                )
            ),
            "visibility": float(
                a.get(
                    "visibility",
                    1.0
                )
            ),
            "confidence": float(
                a.get(
                    "confidence",
                    1.0
                )
            )
        }

    def build_project_dict(self):
        self.commit_current()

        return {
            "app": APP_NAME,
            "version": PROJECT_VERSION,
            "project_name": self.project_name,
            "media_type": self.media_type,
            "video_path": self.video_path,
            "image_paths": self.image_paths,
            "fps": self.fps,
            "total_frames": self.total_frames,
            "classes": {
                str(k): v
                for k, v in self.classes.items()
            },
            "identities": {
                str(k): v
                for k, v in self.identities.items()
            },
            "next_individual_id":
                self.next_individual_id,
            "next_track_id":
                self.next_track_id,
            "annotations": {
                str(k): v
                for k, v in self.annotations.items()
            }
        }

    def save_project(self):
        if not self.total_frames:
            messagebox.showwarning(
                "Save",
                "Open media first."
            )
            return

        if not self.project_file:
            return self.save_project_as()

        try:
            data = self.build_project_dict()

            with open(
                self.project_file,
                "w",
                encoding="utf-8"
            ) as f:
                json.dump(
                    data,
                    f,
                    indent=2,
                    ensure_ascii=False
                )

            self.status_var.set(
                f"Saved: {self.project_file}"
            )

        except Exception as e:
            messagebox.showerror(
                "Save error",
                str(e)
            )

    def save_project_as(self):
        if not self.total_frames:
            messagebox.showwarning(
                "Save",
                "Open media first."
            )
            return

        path = filedialog.asksaveasfilename(
            title="Save Project",
            defaultextension=".json",
            filetypes=[
                ("Rahat Project", "*.json")
            ]
        )

        if not path:
            return

        self.project_file = path
        self.project_dir = str(
            Path(path).parent
        )

        self.save_project()

    def load_project(self):
        path = filedialog.askopenfilename(
            title="Load Project",
            filetypes=[
                ("Rahat Project", "*.json")
            ]
        )

        if not path:
            return

        try:
            with open(
                path,
                "r",
                encoding="utf-8"
            ) as f:
                data = json.load(f)

            self.close_media()

            self.project_file = path
            self.project_dir = str(
                Path(path).parent
            )

            self.project_name = data.get(
                "project_name",
                "Loaded Project"
            )

            self.media_type = data.get(
                "media_type"
            )

            self.video_path = data.get(
                "video_path"
            )

            self.image_paths = data.get(
                "image_paths",
                []
            )

            self.fps = data.get(
                "fps",
                25.0
            )

            self.total_frames = data.get(
                "total_frames",
                0
            )

            self.classes = {
                int(k): v
                for k, v in data.get(
                    "classes",
                    {"0": {"name": "person"}}
                ).items()
            }

            self.identities = {
                int(k): v
                for k, v in data.get(
                    "identities",
                    {}
                ).items()
            }

            self.next_individual_id = int(
                data.get(
                    "next_individual_id",
                    max(
                        self.identities.keys(),
                        default=0
                    ) + 1
                )
            )

            self.next_track_id = int(
                data.get(
                    "next_track_id",
                    1
                )
            )

            self.annotations = {
                int(k): v
                for k, v in data.get(
                    "annotations",
                    {}
                ).items()
            }

            if self.media_type == "video":
                self.cap = cv2.VideoCapture(
                    self.video_path
                )

                if not self.cap.isOpened():
                    raise RuntimeError(
                        "Could not reopen video:\n"
                        f"{self.video_path}"
                    )

            elif self.media_type == "images":
                if not self.image_paths:
                    raise RuntimeError(
                        "Image list is empty."
                    )

            self.refresh_class_list()
            self.refresh_identity_list()

            self.show_frame(0)

            messagebox.showinfo(
                "Loaded",
                "Project loaded successfully."
            )

        except Exception as e:
            messagebox.showerror(
                "Load error",
                str(e)
            )

    # ============================================================
    # EXPORT
    # ============================================================

    def export_yolo(self):
        if not self.total_frames:
            messagebox.showwarning(
                "YOLO",
                "Open media first."
            )
            return

        self.commit_current()

        out = filedialog.askdirectory(
            title="Select YOLO output folder"
        )

        if not out:
            return

        out = Path(out)

        train_ratio = simpledialog.askfloat(
            "Train split",
            "Training ratio:",
            initialvalue=0.8,
            minvalue=0,
            maxvalue=1
        )

        if train_ratio is None:
            return

        val_ratio = simpledialog.askfloat(
            "Validation split",
            "Validation ratio:",
            initialvalue=0.1,
            minvalue=0,
            maxvalue=1
        )

        if val_ratio is None:
            return

        if train_ratio + val_ratio > 1:
            messagebox.showerror(
                "Split",
                "Train + validation must be <= 1."
            )
            return

        use_obb = messagebox.askyesno(
            "Rotated boxes",
            "Export rotated boxes as YOLO-OBB?\n\n"
            "Yes = class x1 y1 x2 y2 x3 y3 x4 y4 (normalized corners)\n"
            "No  = standard YOLO using the axis-aligned envelope"
        )

        indices = list(
            range(self.total_frames)
        )

        random.Random(42).shuffle(
            indices
        )

        n_train = int(
            len(indices) * train_ratio
        )

        n_val = int(
            len(indices) * val_ratio
        )

        splits = {
            "train":
                indices[:n_train],
            "val":
                indices[
                    n_train:
                    n_train+n_val
                ],
            "test":
                indices[
                    n_train+n_val:
                ]
        }

        for split in splits:
            (
                out /
                "images" /
                split
            ).mkdir(
                parents=True,
                exist_ok=True
            )

            (
                out /
                "labels" /
                split
            ).mkdir(
                parents=True,
                exist_ok=True
            )

        exported = 0

        for split, frame_indices in splits.items():
            for idx in frame_indices:
                frame = self.read_frame(idx)

                if frame is None:
                    continue

                h, w = frame.shape[:2]

                if self.media_type == "video":
                    stem = (
                        f"frame_{idx:06d}"
                    )
                else:
                    stem = Path(
                        self.image_paths[idx]
                    ).stem

                image_path = (
                    out /
                    "images" /
                    split /
                    f"{stem}.jpg"
                )

                label_path = (
                    out /
                    "labels" /
                    split /
                    f"{stem}.txt"
                )

                cv2.imwrite(
                    str(image_path),
                    frame
                )

                with open(
                    label_path,
                    "w",
                    encoding="utf-8"
                ) as f:
                    for a in self.annotations.get(
                        idx,
                        []
                    ):
                        if use_obb:
                            pts = self.box_corners(
                                a["bbox"], a.get("angle", 0.0)
                            )
                            flat = " ".join(
                                f"{min(1.0, max(0.0, px / w)):.6f} "
                                f"{min(1.0, max(0.0, py / h)):.6f}"
                                for px, py in pts
                            )
                            f.write(f"{a['class_id']} {flat}\n")
                            continue

                        x1, y1, x2, y2 = self.box_envelope(
                            a["bbox"], a.get("angle", 0.0)
                        )

                        xc = (
                            (x1+x2)/2
                        ) / w

                        yc = (
                            (y1+y2)/2
                        ) / h

                        bw = (
                            x2-x1
                        ) / w

                        bh = (
                            y2-y1
                        ) / h

                        f.write(
                            f"{a['class_id']} "
                            f"{xc:.6f} "
                            f"{yc:.6f} "
                            f"{bw:.6f} "
                            f"{bh:.6f}\n"
                        )

                exported += 1

        names = [
            self.classes[cid]["name"]
            for cid in sorted(
                self.classes
            )
        ]

        yaml_path = (
            out / "data.yaml"
        )

        with open(
            yaml_path,
            "w",
            encoding="utf-8"
        ) as f:
            f.write(
                f"path: {out.resolve().as_posix()}\n"
            )
            f.write(
                "train: images/train\n"
            )
            f.write(
                "val: images/val\n"
            )
            f.write(
                "test: images/test\n"
            )
            f.write(
                f"nc: {len(names)}\n"
            )
            f.write(
                "names: "
                f"{json.dumps(names, ensure_ascii=False)}\n"
            )

        # Save identity metadata separately.
        with open(
            out / "identity_metadata.json",
            "w",
            encoding="utf-8"
        ) as f:
            json.dump(
                {
                    "classes":
                        self.classes,
                    "identities":
                        self.identities
                },
                f,
                indent=2,
                ensure_ascii=False
            )

        messagebox.showinfo(
            "YOLO Export Complete",
            f"Exported {exported} images.\n\n"
            f"Dataset:\n{out}\n\n"
            f"YAML:\n{yaml_path}\n\n"
            "Individual IDs are preserved in "
            "identity_metadata.json and the "
            "project JSON."
        )

    def export_coco(self):
        if not self.total_frames:
            return

        self.commit_current()

        path = filedialog.asksaveasfilename(
            title="Export COCO JSON",
            defaultextension=".json",
            filetypes=[
                ("COCO JSON", "*.json")
            ]
        )

        if not path:
            return

        images = []
        annotations = []

        ann_id = 1

        for idx in sorted(
            self.annotations
        ):
            frame = self.read_frame(idx)

            if frame is None:
                continue

            h, w = frame.shape[:2]

            if self.media_type == "video":
                filename = (
                    f"frame_{idx:06d}.jpg"
                )
            else:
                filename = Path(
                    self.image_paths[idx]
                ).name

            images.append(
                {
                    "id": idx + 1,
                    "file_name": filename,
                    "width": w,
                    "height": h
                }
            )

            for a in self.annotations[idx]:
                angle = a.get("angle", 0.0)
                corners = self.box_corners(a["bbox"], angle)
                x1, y1, x2, y2 = self.box_envelope(a["bbox"], angle)

                bw = x2 - x1
                bh = y2 - y1

                annotations.append(
                    {
                        "id": ann_id,
                        "image_id": idx + 1,
                        "category_id":
                            a["class_id"] + 1,
                        "bbox": [
                            x1, y1, bw, bh
                        ],
                        "area": (
                            (a["bbox"][2] - a["bbox"][0])
                            * (a["bbox"][3] - a["bbox"][1])
                        ),
                        "segmentation": [
                            [v for p in corners for v in p]
                        ],
                        "angle": angle,
                        "rbox": [
                            (a["bbox"][0] + a["bbox"][2]) / 2.0,
                            (a["bbox"][1] + a["bbox"][3]) / 2.0,
                            a["bbox"][2] - a["bbox"][0],
                            a["bbox"][3] - a["bbox"][1],
                            angle,
                        ],
                        "iscrowd": 0,
                        "individual_id":
                            a["individual_id"],
                        "track_id":
                            a.get(
                                "track_id",
                                -1
                            ),
                        "occluded":
                            a.get(
                                "occluded",
                                False
                            ),
                        "visibility":
                            a.get(
                                "visibility",
                                1.0
                            )
                    }
                )

                ann_id += 1

        categories = [
            {
                "id": cid + 1,
                "name":
                    self.classes[cid]["name"],
                "supercategory":
                    "object"
            }
            for cid in sorted(
                self.classes
            )
        ]

        coco = {
            "info": {
                "description":
                    "Rahat Label Studio dataset"
            },
            "images": images,
            "annotations":
                annotations,
            "categories":
                categories
        }

        with open(
            path,
            "w",
            encoding="utf-8"
        ) as f:
            json.dump(
                coco,
                f,
                indent=2,
                ensure_ascii=False
            )

        messagebox.showinfo(
            "COCO Export",
            f"Saved {len(annotations)} "
            f"annotations:\n{path}"
        )

    def export_mot(self):
        if not self.total_frames:
            return

        self.commit_current()

        out = filedialog.askdirectory(
            title="Select MOT output folder"
        )

        if not out:
            return

        out = Path(out)

        gt_dir = (
            out /
            "gt"
        )

        gt_dir.mkdir(
            parents=True,
            exist_ok=True
        )

        gt_path = (
            gt_dir /
            "gt.txt"
        )

        rows = []

        for frame_idx in sorted(
            self.annotations
        ):
            for a in self.annotations[
                frame_idx
            ]:
                x1, y1, x2, y2 = self.box_envelope(
                    a["bbox"], a.get("angle", 0.0)
                )

                width = x2 - x1
                height = y2 - y1

                # MOT frame numbers start at 1.
                frame_number = (
                    frame_idx + 1
                )

                # MOT identity = Individual ID.
                identity = int(
                    a["individual_id"]
                )

                rows.append(
                    [
                        frame_number,
                        identity,
                        x1,
                        y1,
                        width,
                        height,
                        1,
                        a["class_id"],
                        a.get(
                            "visibility",
                            1.0
                        )
                    ]
                )

        with open(
            gt_path,
            "w",
            encoding="utf-8"
        ) as f:
            for row in rows:
                f.write(
                    ",".join(
                        f"{x:.6f}"
                        if isinstance(
                            x, float
                        )
                        else str(x)
                        for x in row
                    )
                    + "\n"
                )

        messagebox.showinfo(
            "MOT Export",
            f"Saved {len(rows)} MOT rows:\n"
            f"{gt_path}"
        )

    # ============================================================
    # ANNOTATED VIDEO EXPORT
    # ============================================================

    @staticmethod
    def _hex_to_bgr(hex_color):
        r, g, b = _hex_rgb(hex_color)
        return (b, g, r)

    @staticmethod
    def _fit_to_size(img, size):
        """Letterbox `img` into `size` (W, H). Used for mixed-size image folders."""
        W, H = size
        h, w = img.shape[:2]
        if (w, h) == (W, H):
            return img
        sc = min(W / w, H / h)
        nw, nh = max(1, int(w * sc)), max(1, int(h * sc))
        resized = cv2.resize(
            img, (nw, nh),
            interpolation=cv2.INTER_AREA if sc < 1 else cv2.INTER_LINEAR
        )
        canvas = np.zeros((H, W, 3), dtype=np.uint8)
        x0, y0 = (W - nw) // 2, (H - nh) // 2
        canvas[y0:y0 + nh, x0:x0 + nw] = resized
        return canvas

    def render_annotated_frame(self, frame, anns):
        """Return a copy of `frame` (BGR) with every box and ID label drawn on it."""
        out = frame.copy()
        h, w = out.shape[:2]
        short = min(h, w)
        thick = max(2, int(round(short / 320.0)))
        font = cv2.FONT_HERSHEY_SIMPLEX
        fscale = max(0.5, short / 900.0)
        ftick = max(1, int(round(fscale * 2)))

        for obj in anns:
            iid = int(obj["individual_id"])
            color = self._hex_to_bgr(
                self.id_colors[(iid - 1) % len(self.id_colors)]
            )
            occluded = bool(obj.get("occluded", False))
            angle = obj.get("angle", 0.0)

            pts = np.array(
                self.box_corners(obj["bbox"], angle), dtype=np.float32
            ).round().astype(np.int32)
            line_w = max(1, thick - 1) if occluded else thick
            cv2.polylines(out, [pts.reshape(-1, 1, 2)], True, color, line_w, cv2.LINE_AA)

            cname = self.classes.get(obj["class_id"], {"name": "unknown"})["name"]
            label = f"ID {iid} | {cname}" + (" (occ)" if occluded else "")
            (tw, th), base = cv2.getTextSize(label, font, fscale, ftick)
            bw, bh = tw + 8, th + base + 6

            lx, ly = int(pts[0][0]), int(pts[0][1])
            x0 = min(max(0, lx), max(0, w - bw))
            y0 = ly - bh                      # label sits above the top-left corner
            if y0 < 0:                        # no room above -> tuck it below
                y0 = min(max(0, ly), max(0, h - bh))

            cv2.rectangle(out, (x0, y0), (x0 + bw, y0 + bh), color, -1)
            lum = 0.114 * color[0] + 0.587 * color[1] + 0.299 * color[2]
            txt_col = (0, 0, 0) if lum > 150 else (255, 255, 255)
            cv2.putText(
                out, label, (x0 + 4, y0 + th + 2),
                font, fscale, txt_col, ftick, cv2.LINE_AA
            )
        return out

    def _finalize_with_ffmpeg(self, ffmpeg, raw_path, out_path, audio_src, pump):
        """Re-encode to H.264 (plays everywhere) and copy the original audio.
        Returns True on success. `pump()` keeps the progress window alive."""
        cmd = [ffmpeg, "-y", "-i", str(raw_path)]
        if audio_src:
            cmd += ["-i", str(audio_src)]
        cmd += ["-map", "0:v:0"]
        if audio_src:
            cmd += ["-map", "1:a:0?", "-c:a", "aac", "-b:a", "192k", "-shortest"]
        cmd += [
            "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18",
            "-preset", "medium",
            "-vf", "scale=trunc(iw/2)*2:trunc(ih/2)*2",
            "-movflags", "+faststart", str(out_path),
        ]
        flags = 0x08000000 if sys.platform.startswith("win") else 0  # no console window
        try:
            proc = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                creationflags=flags
            )
            while proc.poll() is None:
                pump()
                time.sleep(0.05)
            return proc.returncode == 0 and out_path.exists() and out_path.stat().st_size > 0
        except Exception:
            return False

    def export_annotated_video(self):
        if not self.total_frames:
            messagebox.showwarning(
                "Annotated Video", "Open a video or image folder first."
            )
            return

        self.playing = False
        self.commit_current()

        total_boxes = sum(len(a) for a in self.annotations.values())
        if total_boxes == 0 and not messagebox.askyesno(
            "Annotated Video",
            "There are no bounding boxes in this project yet.\n"
            "Export the video anyway?"
        ):
            return

        path = filedialog.asksaveasfilename(
            title="Save annotated video",
            defaultextension=".mp4",
            initialdir=self.project_dir or str(APP_DIR),
            initialfile=f"{self.project_name}_annotated.mp4",
            filetypes=[("MP4 video", "*.mp4"), ("AVI video", "*.avi")],
        )
        if not path:
            return

        out_path = Path(path)
        ext = out_path.suffix.lower()
        if ext not in (".mp4", ".avi"):
            out_path = out_path.with_suffix(".mp4")
            ext = ".mp4"

        if self.media_type == "video":
            fps = max(float(self.fps), 1.0)
            src_cap = cv2.VideoCapture(self.video_path)
            if not src_cap.isOpened():
                messagebox.showerror("Annotated Video", "Could not re-open the source video.")
                return
        else:
            fps = simpledialog.askfloat(
                "Frame rate",
                "Frames per second for the output video:",
                initialvalue=5.0, minvalue=0.1, maxvalue=120, parent=self,
            )
            if fps is None:
                return
            src_cap = None

        ffmpeg = shutil.which("ffmpeg")
        use_ffmpeg = bool(ffmpeg) and ext == ".mp4"
        raw_path = (
            out_path.with_name(out_path.stem + "_raw" + ext) if use_ffmpeg else out_path
        )
        audio_src = self.video_path if self.media_type == "video" else None

        # ---------------- progress window ----------------
        total = self.total_frames
        cancelled = {"v": False}

        prog = tk.Toplevel(self)
        prog.title("Saving annotated video")
        prog.configure(bg=THEME["panel"])
        prog.transient(self)
        prog.resizable(False, False)
        prog.protocol("WM_DELETE_WINDOW", lambda: cancelled.__setitem__("v", True))

        body = ttk.Frame(prog, padding=20)
        body.pack(fill="both", expand=True)
        ttk.Label(body, text="Rendering annotated video", style="Header.TLabel").pack(anchor="w")
        info = ttk.Label(body, text=f"Frame 0 / {total}")
        info.pack(anchor="w", pady=(10, 6))
        bar = ttk.Progressbar(body, length=440, maximum=max(1, total))
        bar.pack(fill="x")
        cancel_btn = ttk.Button(
            body, text="Cancel",
            command=lambda: cancelled.__setitem__("v", True)
        )
        cancel_btn.pack(anchor="e", pady=(14, 0))

        prog.update_idletasks()
        px = self.winfo_rootx() + (self.winfo_width() - prog.winfo_reqwidth()) // 2
        py = self.winfo_rooty() + (self.winfo_height() - prog.winfo_reqheight()) // 3
        prog.geometry(f"+{max(0, px)}+{max(0, py)}")
        try:
            prog.grab_set()
        except tk.TclError:
            pass

        writer = None
        size = None
        written = 0
        error = None

        try:
            for idx in range(total):
                if cancelled["v"]:
                    break

                if src_cap is not None:
                    ok, frame = src_cap.read()
                    if not ok:
                        break          # file has fewer frames than its header claims
                else:
                    frame = cv2.imread(self.image_paths[idx])
                    if frame is None:
                        continue

                out = self.render_annotated_frame(frame, self.annotations.get(idx, []))

                if writer is None:
                    size = (out.shape[1], out.shape[0])
                    fourcc = cv2.VideoWriter_fourcc(*("mp4v" if ext == ".mp4" else "XVID"))
                    writer = cv2.VideoWriter(str(raw_path), fourcc, fps, size)
                    if not writer.isOpened():
                        raise RuntimeError(
                            "Could not create the output video.\n"
                            "Check that the folder is writable."
                        )
                else:
                    out = self._fit_to_size(out, size)

                writer.write(out)
                written += 1

                if idx % 4 == 0 or idx == total - 1:
                    bar["value"] = idx + 1
                    info.config(text=f"Frame {idx + 1} / {total}")
                    prog.update()
        except Exception as e:
            error = e
        finally:
            if writer is not None:
                writer.release()
            if src_cap is not None:
                src_cap.release()

        def cleanup(*paths):
            for p in paths:
                try:
                    Path(p).unlink()
                except Exception:
                    pass

        if error is not None or cancelled["v"] or written == 0:
            prog.grab_release()
            prog.destroy()
            cleanup(raw_path)
            if error is not None:
                messagebox.showerror("Annotated Video", f"Export failed:\n{error}")
            elif cancelled["v"]:
                messagebox.showinfo("Annotated Video", "Export cancelled.")
            else:
                messagebox.showerror("Annotated Video", "No frames could be read.")
            return

        note = ""
        if use_ffmpeg:
            info.config(text="Finalizing (H.264 + audio)...")
            cancel_btn.state(["disabled"])
            bar.config(mode="indeterminate")
            bar.start(12)
            prog.update()
            ok = self._finalize_with_ffmpeg(
                ffmpeg, raw_path, out_path, audio_src, pump=prog.update
            )
            bar.stop()
            if ok:
                cleanup(raw_path)
                note = "H.264 video" + (" with original audio." if audio_src else ".")
            else:
                cleanup(out_path)
                try:
                    shutil.move(str(raw_path), str(out_path))
                except Exception:
                    out_path = raw_path
                note = "ffmpeg failed, so this is a basic MP4 without audio."
        else:
            note = (
                "Saved without audio. Install ffmpeg (and add it to PATH) to get "
                "H.264 + original audio."
                if self.media_type == "video" else ""
            )

        prog.grab_release()
        prog.destroy()

        self.status_var.set(f"Annotated video saved: {out_path}")
        messagebox.showinfo(
            "Annotated Video",
            f"Saved {written} frames to:\n{out_path}\n\n{note}".rstrip()
        )

    # ============================================================
    # STATUS / HELP
    # ============================================================

    def update_status(self):
        if self.total_frames:
            self.frame_label.config(
                text=(
                    f"{self.frame_idx+1} / "
                    f"{self.total_frames}"
                )
            )

            self.frame_var.set(
                str(self.frame_idx + 1)
            )

            self.timeline.configure(
                to=max(
                    1,
                    self.total_frames - 1
                )
            )

            current_time = (
                self.frame_idx /
                max(self.fps, 1)
            )

            total_time = (
                max(
                    0,
                    self.total_frames - 1
                ) /
                max(self.fps, 1)
            )

            self.time_label.config(
                text=(
                    f"{self.format_time(current_time)}"
                    " / "
                    f"{self.format_time(total_time)}"
                )
            )

            annotated_frames = sum(
                1
                for anns in
                self.annotations.values()
                if anns
            )

            box_count = sum(
                len(anns)
                for anns in
                self.annotations.values()
            )

            self.project_info.set(
                f"Project: {self.project_name}\n"
                f"Frames: {self.total_frames}\n"
                f"Annotated frames: {annotated_frames}\n"
                f"Boxes: {box_count}\n"
                f"Classes: {len(self.classes)}\n"
                f"Individual IDs: "
                f"{len(self.identities)}"
            )

            self.status_var.set(
                f"Frame {self.frame_idx+1}/"
                f"{self.total_frames} | "
                f"Active class: "
                f"{self.classes.get(self.active_class_id, {'name':'?'})['name']} | "
                f"Active ID: "
                f"{self.active_individual_id} | "
                f"Objects: "
                f"{len(self.current_boxes)}"
            )

            self.timeline.set(
                self.frame_idx
            )
        else:
            self.status_var.set(
                "Open a video or image folder to begin."
            )

    @staticmethod
    def format_time(seconds):
        seconds = int(
            max(0, seconds)
        )

        return (
            f"{seconds // 60:02d}:"
            f"{seconds % 60:02d}"
        )

    def show_help(self):
        messagebox.showinfo(
            "Keyboard Shortcuts",
            "Arrow Left       Previous frame\n"
            "Arrow Right      Next frame\n"
            "Space             Play / Pause\n"
            "1–9               Select Individual ID 1–9\n"
            "S                 Save project\n"
            "Ctrl+E            Export annotated video\n"
            "C                 Copy previous frame\n"
            "X                 Clear frame\n"
            "Delete/Backspace  Delete selected object\n\n"
            "Mouse:\n"
            "Drag empty area = create bounding box\n"
            "Drag object     = move bounding box\n"
            "Right click     = select object\n\n"
            "Workflow:\n"
            "1. Create classes.\n"
            "2. Create Individual IDs.\n"
            "3. Select class + ID.\n"
            "4. Draw the person's box.\n"
            "5. Draw once, assign the ID, then use Track Forward.\n"
            "6. Review and correct.\n"
            "7. Export YOLO/COCO/MOT, or Save Video for the annotated video."
        )

    def show_ai_guide(self):
        messagebox.showinfo(
            "AI Integration",
            "The project structure is ready for AI-assisted annotation.\n\n"
            "Recommended next integrations:\n"
            "1. RahatDet / YOLO automatic detection\n"
            "2. BoT-SORT or ByteTrack\n"
            "3. ViT/OSNet appearance embedding\n"
            "4. Global Individual-ID association\n"
            "5. Human verification before saving\n\n"
            "The Individual ID is the persistent research identity."
        )

    def show_stats(self):
        annotated_frames = sum(
            1
            for anns in
            self.annotations.values()
            if anns
        )

        total_boxes = sum(
            len(anns)
            for anns in
            self.annotations.values()
        )

        ids = sorted(
            {
                a["individual_id"]
                for anns in
                self.annotations.values()
                for a in anns
            }
        )

        classes = sorted(
            {
                a["class_id"]
                for anns in
                self.annotations.values()
                for a in anns
            }
        )

        messagebox.showinfo(
            "Project Statistics",
            f"Frames: {self.total_frames}\n"
            f"Annotated frames: {annotated_frames}\n"
            f"Bounding boxes: {total_boxes}\n"
            f"Individual IDs: {len(ids)}\n"
            f"Classes used: {len(classes)}\n\n"
            f"IDs: {ids}"
        )

    def show_about(self):
        messagebox.showinfo(
            "About",
            "Rahat Label Studio v2\n"
            "Developed by MD.RAHATUL ISLAM\n\n"
            "Identity-aware annotation software "
            "for detection, tracking and Re-ID datasets.\n\n"
            "Class and Individual ID are stored separately."
        )

    # ============================================================
    # CLOSE
    # ============================================================

    def on_close(self):
        if self.total_frames:
            result = messagebox.askyesnocancel(
                "Exit",
                "Save project before closing?"
            )

            if result is None:
                return

            if result:
                self.save_project()

        self.playing = False
        self.close_media()
        self.destroy()


if __name__ == "__main__":
    app = RahatLabelStudio()
    app.mainloop()