#!/usr/bin/env python3
import os
import argparse
import re
import sys
from typing import List, Tuple, Optional, Dict

import numpy as np
import matplotlib.pyplot as plt

# --- parsing helpers ----------------------------------------------------------

PM_RE = re.compile(
    r'^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s*±\s*'
    r'([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s*$'
)
DASH_RE = re.compile(r'^\s*-{5,}\s*$')
T_LINE_RE = re.compile(r'^\s*t\s*=.*"([^"]*)".*$')
YT_LINE_RE = re.compile(r'^\s*y\(t\)\s*=')

MODE_KEYS = {
    "1": "time_series",
    "2": "phase_space",
    "3": "both",
    "4": "scatter",
    "5": "step_size",
    "6": "width",
}

def print_mode_help():
    msg = (
        "\n[interactive controls]\n"
        "  1 = time_series\n"
        "  2 = phase_space\n"
        "  3 = both\n"
        "  4 = scatter\n"
        "  5 = step_size\n"
        "  6 = width\n"
        "  h or ? = this help\n"
    )
    print(msg, file=sys.stderr, flush=True)

def parse_pm_interval(s: str) -> Tuple[float, float]:
    m = PM_RE.match(s)
    if not m:
        raise ValueError(f"Cannot parse center±radius: '{s}'")
    c = float(m.group(1)); r = float(m.group(2))
    return (c - r, c + r)

def parse_header(text: str) -> Dict[str, str]:
    """(Kept for compatibility) Parse the first dashed header block into a dict."""
    lines = text.splitlines()
    i = 0
    n = len(lines)
    header: Dict[str, str] = {}
    while i < n and not DASH_RE.match(lines[i]):
        i += 1
    if i >= n:
        return header
    i += 1
    while i < n and not DASH_RE.match(lines[i]):
        line = lines[i].strip()
        if line and ':' in line:
            k, v = line.split(':', 1)
            header[k.strip()] = v.strip()
        i += 1
    return header

def extract_blocks(text: str) -> List[Tuple[str, List[str]]]:
    """
    Extract blocks of (t_str, y_tokens) from the file content.
    Robust to y-list being on the same line as 'y(t) ='.
    """
    lines = text.splitlines()
    i = 0
    n = len(lines)
    blocks: List[Tuple[str, List[str]]] = []
    while i < n:
        line = lines[i]
        m_t = T_LINE_RE.match(line)
        if m_t:
            t_str = m_t.group(1)
            # find the y(t) line
            i += 1
            while i < n and not YT_LINE_RE.match(lines[i]):
                if T_LINE_RE.match(lines[i]) or DASH_RE.match(lines[i]):
                    i -= 1
                    break
                i += 1
            if i >= n or not YT_LINE_RE.match(lines[i]):
                i += 1
                continue

            # Collect tokens on the y(t) line itself (after '='), plus subsequent lines
            y_line = lines[i]
            after_eq = y_line.split('=', 1)[1] if '=' in y_line else ''
            vec_chunks = [after_eq]

            i += 1  # gather continuation lines until boundary
            while i < n:
                if DASH_RE.match(lines[i]) or T_LINE_RE.match(lines[i]) or YT_LINE_RE.match(lines[i]):
                    i -= 1
                    break
                vec_chunks.append(lines[i])
                i += 1

            vec_text = '\n'.join(vec_chunks)
            tokens = re.findall(r'"([^"]+)"', vec_text)
            if tokens:
                blocks.append((t_str, tokens))
        i += 1
    return blocks

def accumulate_series(blocks: List[Tuple[str, List[str]]]) -> Tuple[np.ndarray, np.ndarray, List[np.ndarray], List[np.ndarray]]:
    t_lo: List[float] = []
    t_hi: List[float] = []
    lowers: Optional[List[List[float]]] = None
    uppers: Optional[List[List[float]]] = None
    for t_str, y_tokens in blocks:
        lo_t, hi_t = parse_pm_interval(t_str)
        t_lo.append(lo_t); t_hi.append(hi_t)
        if lowers is None:
            m = len(y_tokens)
            lowers = [[] for _ in range(m)]
            uppers = [[] for _ in range(m)]
        # keep component count consistent
        if len(y_tokens) != len(lowers):
            m2 = min(len(y_tokens), len(lowers))
            y_tokens = y_tokens[:m2]  # type: ignore[index]
        for j, tok in enumerate(y_tokens):
            lo, hi = parse_pm_interval(tok)
            lowers[j].append(lo)      # type: ignore[index]
            uppers[j].append(hi)      # type: ignore[index]
    if lowers is None:
        raise ValueError("No data blocks parsed.")
    return (np.array(t_lo), np.array(t_hi),
            [np.array(L) for L in lowers],
            [np.array(U) for U in uppers])

# --- plotting helpers ---------------------------------------------------------

def plot_time_series(ax, t_lo, t_hi, lowers, uppers, names, title):
    t_mid = 0.5 * (t_lo + t_hi)
    ax.clear()
    for j in range(len(lowers)):
        y_lo, y_hi = lowers[j], uppers[j]
        y_mid = 0.5 * (y_lo + y_hi)
        ax.fill_between(t_mid, y_lo, y_hi, alpha=0.3, label='_nolegend_')
        ax.plot(t_mid, y_mid, linewidth=1, label=names[j])
    ax.set_xlabel("Time")
    ax.set_ylabel("Value")
    ax.set_title(title)
    ax.legend()

def plot_phase_space(ax, lowers, uppers, names, title):
    ax.clear()
    mids = [(l + u) / 2 for l, u in zip(lowers, uppers)]
    if len(mids) >= 3 and getattr(ax, "name", "") == "3d":
        ax.plot(mids[0], mids[1], mids[2], lw=0.5)
        ax.scatter(mids[0][0], mids[1][0], mids[2][0], marker='o', s=10)
        ax.set_xlabel(names[0]); ax.set_ylabel(names[1]); ax.set_zlabel(names[2])
        ax.set_title(title)
        return
    if len(mids) >= 2:
        ax.plot(mids[0], mids[1], lw=0.5)
        ax.scatter(mids[0][0], mids[1][0], marker='o', s=10)
        ax.set_xlabel(names[0]); ax.set_ylabel(names[1])
        ax.set_title(title)
        return
    # M == 1: cannot do phase space meaningfully
    ax.text(0.5, 0.5, "Phase space needs ≥2 components",
            transform=ax.transAxes, ha='center', va='center')
    ax.set_axis_off()
    ax.set_title(title)

def plot_scatter(ax, t_lo, t_hi, lowers, uppers, names, title):
    ax.clear()
    t_mid = 0.5 * (t_lo + t_hi)
    for j in range(len(lowers)):
        y_mid = 0.5 * (lowers[j] + uppers[j])
        ax.scatter(t_mid, y_mid, s=20, label=names[j])
    ax.set_xlabel("Time")
    ax.set_ylabel("Value")
    ax.set_title(f"{title} (scatter)")
    ax.legend()

def plot_step_size(ax, t_lo, t_hi, title):
    ax.clear()
    t_mid = 0.5 * (t_lo + t_hi)
    if len(t_mid) >= 2:
        dt = np.diff(t_mid)
        ax.plot(t_mid[1:], dt, linestyle='-')
    ax.set_xlabel("Time")
    ax.set_ylabel("Step size Δt")
    ax.set_title(f"{title} (step size)")

def plot_width(ax, t_lo, t_hi, lowers, uppers, names, title):
    ax.clear()
    t_mid = 0.5 * (t_lo + t_hi)
    for j in range(len(lowers)):
        w = uppers[j] - lowers[j]
        ax.plot(t_mid, w, linewidth=1, label=names[j])
    ax.set_xlabel("Time")
    ax.set_ylabel("Interval width")
    ax.set_title(f"{title} (width)")
    ax.legend()

def rebuild_axes(fig, mode, M):
    if mode == "both":
        ax_time = fig.add_subplot(2, 1, 1)
        if M >= 3:
            ax_phase = fig.add_subplot(2, 1, 2, projection='3d')
        else:
            ax_phase = fig.add_subplot(2, 1, 2)
        return (ax_time, ax_phase), "both"
    else:
        if mode == "phase_space" and M >= 3:
            ax = fig.add_subplot(1, 1, 1, projection='3d')
        else:
            ax = fig.add_subplot(1, 1, 1)
        return (ax,), mode

def try_read_stdin_line() -> Optional[str]:
    """Non-blocking read of a line from stdin; returns None if no input available."""
    try:
        import select
        r, _, _ = select.select([sys.stdin], [], [], 0.0)
        if r:
            return sys.stdin.readline()
        return None
    except Exception:
        return None

# --- main loop ---------------------------------------------------------------

def monitor_and_plot(filepath: str, mode: str, title: str, names: List[str],
                     poll_interval: float, no_focus: bool):
    last_mtime = None
    last_mode = None

    fig = plt.figure()
    if not no_focus:
        # default interactive behavior
        plt.ion()
        plt.show(block=False)
    # else: no interactive forcing; window won’t jump to front

    axes = ()
    print_mode_help()

    while True:
        # (1) interactive mode switch
        line = try_read_stdin_line()
        if line is not None:
            key = line.strip()
            if key in ("h", "?"):
                print_mode_help()
            elif key in MODE_KEYS:
                new_mode = MODE_KEYS[key]
                if new_mode != mode:
                    mode = new_mode
                    print(f"[mode] -> {mode}", file=sys.stderr, flush=True)
                    last_mode = None
            elif key != "":
                print(f"[ignored input] '{key}' (press h for help)", file=sys.stderr, flush=True)

        # (2) file updates
        try:
            mtime = os.path.getmtime(filepath)
        except OSError:
            plt.pause(poll_interval); continue

        if last_mtime is None or mtime > last_mtime or last_mode is None:
            last_mtime = mtime
            try:
                with open(filepath, encoding='utf-8') as f:
                    content = f.read()
            except Exception as e:
                print(f"[Error] Failed to read file: {e}", file=sys.stderr)
                plt.pause(poll_interval); continue

            try:
                blocks = extract_blocks(content)
                if not blocks:
                    plt.pause(poll_interval); continue
                t_lo, t_hi, lowers, uppers = accumulate_series(blocks)
            except Exception as e:
                print(f"[Error] {e}", file=sys.stderr)
                plt.pause(poll_interval); continue

            M = len(lowers)
            if len(names) < M:
                names = names + [f"Component {i+1}" for i in range(len(names), M)]
            else:
                names = names[:M]

            if mode != last_mode:
                fig.clf()
                axes, last_mode = rebuild_axes(fig, mode, M)

            # draw
            if mode == "time_series":
                plot_time_series(axes[0], t_lo, t_hi, lowers, uppers, names, title)
            elif mode == "phase_space":
                plot_phase_space(axes[0], lowers, uppers, names, title)
            elif mode == "scatter":
                plot_scatter(axes[0], t_lo, t_hi, lowers, uppers, names, title)
            elif mode == "step_size":
                plot_step_size(axes[0], t_lo, t_hi, title)
            elif mode == "width":
                plot_width(axes[0], t_lo, t_hi, lowers, uppers, names, title)
            else:  # both
                fig.suptitle(title)
                ax_time, ax_phase = axes
                plot_time_series(ax_time, t_lo, t_hi, lowers, uppers, names, "Time Series")
                # phase-space subplot reuses helper which handles 1D/2D/3D gracefully
                plot_phase_space(ax_phase, lowers, uppers, names, "Phase Space")

            fig.canvas.draw()

        plt.pause(poll_interval)  # keeps GUI responsive without stealing focus

def main():
    parser = argparse.ArgumentParser(
        description="Live-plot intervals from Coq tactic output (center±radius format). Press 1..6 to change modes."
    )
    parser.add_argument("--file", "-f", required=True, help="Path to the Coq output file to watch")
    parser.add_argument("--mode", "-m", default="time_series",
                        choices=["time_series", "phase_space", "both", "scatter", "step_size", "width"],
                        help="Initial plot mode (you can change it interactively: 1..6)")
    parser.add_argument("--title", "-t", default="Trajectory", help="Plot title")
    parser.add_argument("--names", "-n", default="", help="Comma-separated component names (e.g., 'x,y,z')")
    parser.add_argument("--poll", "-p", type=float, default=0.5, help="Polling interval in seconds")
    parser.add_argument("--no-focus", action="store_true",
                        help="Do not enable interactive mode or raise the window; keep it in the background")
    args = parser.parse_args()

    names = [s.strip() for s in args.names.split(",")] if args.names.strip() else []
    print(f"Watching '{args.file}' (mode={args.mode}) — Ctrl-C to quit.", file=sys.stderr)
    if args.no_focus:
        print("[no-focus] Window will not be raised; it will update quietly.", file=sys.stderr)
    monitor_and_plot(args.file, args.mode, args.title, names, args.poll, args.no_focus)

if __name__ == "__main__":
    main()
