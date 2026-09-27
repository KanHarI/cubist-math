# Usage: python3 tools/homotopy-drawings.py > figures.json (SVG figures for web/reference/cubical.html).
# Generates the homotopy drawings of the cubical chapter: squares in the
# (i, j) plane, i to the right and j upwards.
import html
X0, Y0, S = 44, 32, 150          # square's top-left corner and side, in SVG units
def pt(i, j): return (X0 + S * i, Y0 + S * (1 - j))
def esc(t): return html.escape(t, quote=False)

def square(fid, corners, edges, contours=None, diagonal=None, title=""):
    out = [f'<svg viewBox="0 0 240 232" role="img" aria-labelledby="{fid}-title">',
           f'<title id="{fid}-title">{esc(title)}</title>',
           f'<defs><marker id="{fid}-arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
           '<path d="M0,0 L10,5 L0,10 z" class="arrowhead"/></marker></defs>']
    (x0, y0), (x1, y1) = pt(0, 1), pt(1, 0)
    out.append(f'<rect x="{x0}" y="{y0}" width="{S}" height="{S}" class="face"/>')
    for c in (contours or {}).get("levels", []):
        kind = contours["kind"]
        if kind == "meet":        # min(i, j) = c
            pts = [pt(c, 1), pt(c, c), pt(1, c)]
        elif kind == "join":      # max(i, j) = c
            pts = [pt(0, c), pt(c, c), pt(c, 0)]
        elif kind == "meet-down": # min(i, 1 - j) = c
            pts = [pt(c, 0), pt(c, 1 - c), pt(1, 1 - c)]
        out.append('<polyline points="' + " ".join(f"{a:.1f},{b:.1f}" for a, b in pts) + '" class="level"/>')
    if diagonal:
        (a, b), (c, d) = pt(0, 0), pt(1, 1)
        out.append(f'<line x1="{a}" y1="{b}" x2="{c}" y2="{d}" class="diagonal"/>')
        mx, my = pt(0.6, 0.47)
        out.append(f'<text x="{mx}" y="{my}" class="diagonal-label">{esc(diagonal)}</text>')
    # Edges: (start, end, label position, anchor) along increasing i or j.
    geometry = {
        "bottom": (pt(0, 0), pt(1, 0), (X0 + S / 2, Y0 + S + 20), "middle"),
        "top": (pt(0, 1), pt(1, 1), (X0 + S / 2, Y0 - 10), "middle"),
        "left": (pt(0, 0), pt(0, 1), (X0 - 8, Y0 + S / 2 + 4), "end"),
        "right": (pt(1, 0), pt(1, 1), (X0 + S + 8, Y0 + S / 2 + 4), "start"),
    }
    for side, (label, kind) in edges.items():
        (a, b), (c, d), (lx, ly), anchor = geometry[side]
        # Stop short of the corner so the arrowhead shows.
        if kind == "path":
            dx, dy = c - a, d - b
            n = (dx * dx + dy * dy) ** 0.5
            c2, d2 = c - dx / n * 6, d - dy / n * 6
            out.append(f'<line x1="{a}" y1="{b}" x2="{c2:.1f}" y2="{d2:.1f}" class="edge" marker-end="url(#{fid}-arrow)"/>')
        else:
            out.append(f'<line x1="{a}" y1="{b}" x2="{c}" y2="{d}" class="constant"/>')
        out.append(f'<text x="{lx}" y="{ly}" text-anchor="{anchor}" class="{"label" if kind == "path" else "label faint"}">{esc(label)}</text>')
    offsets = {"bl": (0, 0, -8, 16, "end"), "br": (1, 0, 8, 16, "start"), "tl": (0, 1, -8, -6, "end"), "tr": (1, 1, 8, -6, "start")}
    for key, label in corners.items():
        i, j, dx, dy, anchor = offsets[key]
        a, b = pt(i, j)
        out.append(f'<circle cx="{a}" cy="{b}" r="3" class="corner"/>')
        out.append(f'<text x="{a + dx}" y="{b + dy}" text-anchor="{anchor}" class="point">{esc(label)}</text>')
    # Axes: i to the right under the square, j upwards at its left.
    ax, ay = X0, Y0 + S + 38
    out.append(f'<line x1="{ax}" y1="{ay}" x2="{ax + 34}" y2="{ay}" class="axis" marker-end="url(#{fid}-arrow)"/>'
               f'<text x="{ax + 40}" y="{ay + 4}" class="axis-label">i</text>')
    bx, by = X0 - 30, Y0 + S + 38
    out.append(f'<line x1="{bx}" y1="{by}" x2="{bx}" y2="{by - 34}" class="axis" marker-end="url(#{fid}-arrow)"/>'
               f'<text x="{bx - 4}" y="{by - 40}" text-anchor="middle" class="axis-label">j</text>')
    out.append("</svg>")
    return "".join(out)

def figure(svg, caption):
    return f'              <figure>{svg}<figcaption>{caption}</figcaption></figure>\n'

L = [0.25, 0.5, 0.75]
figs = {}
figs["generic"] = figure(square("h-generic", {"bl": "x", "br": "y", "tl": "x", "tr": "y"},
    {"bottom": ("p", "path"), "top": ("q", "path"), "left": ("x", "constant"), "right": ("y", "constant")},
    title="A square from p to q whose sides stay at x and y"),
    "<code>h : p = q</code>: at <code>j = 0</code> it is <code>p</code>, at <code>j = 1</code> it is <code>q</code>, and its sides stay at <code>x</code> and <code>y</code>.")
figs["meet"] = figure(square("h-meet", {"bl": "x", "br": "x", "tl": "x", "tr": "y"},
    {"bottom": ("x", "constant"), "left": ("x", "constant"), "top": ("p", "path"), "right": ("p", "path")},
    {"kind": "meet", "levels": L}, diagonal="p", title="The square p @ i & j"),
    "<code>p @ i &amp; j</code>. Its diagonal, where <code>i = j</code>, is <code>p</code>.")
figs["join"] = figure(square("h-join", {"bl": "x", "br": "y", "tl": "y", "tr": "y"},
    {"bottom": ("p", "path"), "left": ("p", "path"), "top": ("y", "constant"), "right": ("y", "constant")},
    {"kind": "join", "levels": L}, diagonal="p", title="The square p @ i | j"),
    "<code>p @ i | j</code>. Its diagonal is <code>p</code> as well.")
figs["unit"] = figure(square("h-unit", {"bl": "x", "br": "y", "tl": "x", "tr": "y"},
    {"bottom": ("p", "path"), "top": ("refl(x) ++ p", "path"), "left": ("x", "constant"), "right": ("y", "constant")},
    title="The goal of left_unit"),
    "The goal of <code>left_unit</code>: from <code>p</code> to <code>refl(x) ++ p</code>.")
figs["cancel"] = figure(square("h-cancel", {"bl": "x", "br": "x", "tl": "x", "tr": "x"},
    {"bottom": ("p ++ -p", "path"), "top": ("x", "constant"), "left": ("x", "constant"), "right": ("x", "constant")},
    title="The goal of right_cancel"),
    "The goal of <code>right_cancel</code>: from <code>p ++ -p</code>, out along <code>p</code> and back, to staying at <code>x</code>.")
figs["base"] = figure(square("h-base", {"bl": "x", "br": "y", "tl": "x", "tr": "x"},
    {"bottom": ("p", "path"), "top": ("x", "constant"), "left": ("x", "constant"), "right": ("-p", "path")},
    {"kind": "meet-down", "levels": L}, title="The starting square p @ i & -j"),
    "The square both proofs start from, <code>p @ i &amp; -j</code>: <code>p</code> shrinking back to <code>x</code> as <code>j</code> grows.")
import json, sys
json.dump(figs, sys.stdout)
