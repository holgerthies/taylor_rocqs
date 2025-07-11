#!/usr/bin/env python3
import os
import time
import re

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # enable 3D projection

# Matches "⟦lo,hi⟧" for intervals using Unicode double brackets
INTERVAL_RE = re.compile(
    r'⟦\s*'
    r'([+-]?\d+(?:\.\d*)?(?:[eE][+-]?\d+)?)\s*,\s*'
    r'([+-]?\d+(?:\.\d*)?(?:[eE][+-]?\d+)?)'
    r'\s*⟧'
)

def parse_interval_tokens(tokens):
    ivs = []
    for tok in tokens:
        m = INTERVAL_RE.fullmatch(tok)
        if not m:
            raise ValueError(f"Cannot parse interval '{tok}'")
        ivs.append((float(m.group(1)), float(m.group(2))))
    return ivs

def parse_segment(seg):
    text = seg.strip()
    if not text:
        return None
    tokens = text.split()
    return parse_interval_tokens(tokens)

def load_interval_data(data_segs):
    times_lo, times_hi = [], []
    lowers, uppers = None, None
    for seg in data_segs:
        ivs = parse_segment(seg)
        if ivs is None:
            continue
        t_lo, t_hi = ivs[0]
        times_lo.append(t_lo)
        times_hi.append(t_hi)
        vals = ivs[1:]
        if lowers is None:
            M = len(vals)
            lowers = [[] for _ in range(M)]
            uppers = [[] for _ in range(M)]
        for j, (lo, hi) in enumerate(vals):
            lowers[j].append(lo)
            uppers[j].append(hi)
    if lowers is None:
        raise ValueError("No data segments after parameters")
    return (np.array(times_lo), np.array(times_hi),
            [np.array(L) for L in lowers],
            [np.array(U) for U in uppers])

def monitor_and_plot(filepath, poll_interval=1.0):
    last_mtime = None
    last_mode = None
    fig = plt.figure()
    plt.ion()
    plt.show(block=False)
    axes = ()

    while True:
        try:
            mtime = os.path.getmtime(filepath)
        except OSError:
            plt.pause(poll_interval)
            continue

        if last_mtime is None or mtime > last_mtime:
            last_mtime = mtime
            content = open(filepath, encoding='utf-8').read()

            # extract quoted content if present
            m = re.search(r'"(.*)"', content, re.DOTALL)
            raw = m.group(1) if m else content

            segments = [s.strip() for s in raw.split(';') if s.strip()]
            if len(segments) < 4:
                print("[Error] Need at least mode; title; names; and ≥1 data segment")
                plt.pause(poll_interval)
                continue

            mode_str = segments[0].lower()
            mode = mode_str if mode_str in (
                "time_series", "phase_space", "both", "scatter", "step_size", "width"
            ) else "time_series"
            title = segments[1]
            names = [n.strip() for n in segments[2].split(',')]
            data_segs = segments[3:]

            try:
                t_lo, t_hi, lowers, uppers = load_interval_data(data_segs)
            except Exception as e:
                print(f"[Error] {e}")
                plt.pause(poll_interval)
                continue

            M = len(lowers)
            if len(names) < M:
                names += [f"Component {i+1}" for i in range(len(names), M)]

            # rebuild axes if mode changed
            if mode != last_mode:
                fig.clf()
                if mode == "both":
                    ax_time = fig.add_subplot(2, 1, 1)
                    if M >= 3:
                        ax_phase = fig.add_subplot(2, 1, 2, projection='3d')
                    else:
                        ax_phase = fig.add_subplot(2, 1, 2)
                    axes = (ax_time, ax_phase)
                else:
                    if mode == "phase_space" and M >= 3:
                        ax = fig.add_subplot(1, 1, 1, projection='3d')
                    else:
                        ax = fig.add_subplot(1, 1, 1)
                    axes = (ax,)
                last_mode = mode

            # draw
            if mode == "time_series":
                ax = axes[0]
                ax.clear()
                t_mid = 0.5 * (t_lo + t_hi)
                for j in range(M):
                    y_lo, y_hi = lowers[j], uppers[j]
                    y_mid = 0.5 * (y_lo + y_hi)
                    ax.fill_between(t_mid, y_lo, y_hi, alpha=0.3, label='_nolegend_')
                    ax.plot(t_mid, y_mid, linewidth=1, label=names[j])
                ax.set_xlabel("Time")
                ax.set_ylabel("Value")
                ax.set_title(title)
                ax.legend()

            elif mode == "phase_space":
                ax = axes[0]
                ax.clear()
                mids = [(l + u) / 2 for l, u in zip(lowers, uppers)]
                if M >= 3 and hasattr(ax, 'plot') and ax.name == '3d':
                    ax.plot(mids[0], mids[1], mids[2], lw=0.5)
                    ax.scatter(mids[0][0], mids[1][0], mids[2][0],
                               color='red', marker='o', s=10, label='_nolegend_')
                    ax.set_xlabel(names[0])
                    ax.set_ylabel(names[1])
                    ax.set_zlabel(names[2])
                else:
                    ax.plot(mids[0], mids[1], lw=0.5)
                    ax.scatter(mids[0][0], mids[1][0],
                               color='red', marker='o', s=10, label='_nolegend_')
                    ax.set_xlabel(names[0])
                    ax.set_ylabel(names[1])
                ax.set_title(title)

            elif mode == "scatter":
                ax = axes[0]
                ax.clear()
                t_mid = 0.5 * (t_lo + t_hi)
                for j in range(M):
                    y_mid = 0.5 * (lowers[j] + uppers[j])
                    ax.scatter(t_mid, y_mid, s=20, label=names[j])
                ax.set_xlabel("Time")
                ax.set_ylabel("Value")
                ax.set_title(f"{title} (scatter)")
                ax.legend()

            elif mode == "step_size":
                ax = axes[0]
                ax.clear()
                t_mid = 0.5 * (t_lo + t_hi)
                dt = np.diff(t_mid)
                ax.plot(t_mid[1:], dt, linestyle='-')
                ax.set_xlabel("Time")
                ax.set_ylabel("Step size Δt")
                ax.set_title(f"{title} (step size)")
            elif mode == "width":
                ax = axes[0]
                ax.clear()
                t_mid = 0.5 * (t_lo + t_hi)
                for j in range(M):
                    w = uppers[j] - lowers[j]
                    ax.plot(t_mid, w, linewidth=1, label=names[j])
                ax.set_xlabel("Time")
                ax.set_ylabel("Interval width")
                ax.set_title(f"{title} (width)")
                ax.legend()
                

            else:  # both
                ax_time, ax_phase = axes
                fig.suptitle(title)
                # time series subplot
                ax_time.clear()
                t_mid = 0.5 * (t_lo + t_hi)
                for j in range(M):
                    y_lo, y_hi = lowers[j], uppers[j]
                    y_mid = 0.5 * (y_lo + y_hi)
                    ax_time.fill_between(t_mid, y_lo, y_hi, alpha=0.3, label='_nolegend_')
                    ax_time.plot(t_mid, y_mid, linewidth=1, label=names[j])
                ax_time.set_xlabel("Time")
                ax_time.set_ylabel("Value")
                ax_time.set_title("Time Series")
                ax_time.legend()
                # phase-space subplot
                ax_phase.clear()
                mids = [(l + u) / 2 for l, u in zip(lowers, uppers)]
                if M >= 3 and hasattr(ax_phase, 'plot') and ax_phase.name == '3d':
                    ax_phase.plot(mids[0], mids[1], mids[2], lw=0.5)
                    ax_phase.scatter(mids[0][0], mids[1][0], mids[2][0],
                                     color='red', marker='o', s=10, label='_nolegend_')
                    ax_phase.set_xlabel(names[0])
                    ax_phase.set_ylabel(names[1])
                    ax_phase.set_zlabel(names[2])
                else:
                    ax_phase.plot(mids[0], mids[1], lw=0.5)
                    ax_phase.scatter(mids[0][0], mids[1][0],
                                     color='red', marker='o', s=10, label='_nolegend_')
                    ax_phase.set_xlabel(names[0])
                    ax_phase.set_ylabel(names[1])
                ax_phase.set_title("Phase Space")

            fig.canvas.draw()

        plt.pause(poll_interval)

if __name__ == "__main__":
    DATA_FILE = "data.out"
    POLL_INTERVAL = 1.0
    print(f"Watching '{DATA_FILE}' for changes (Ctrl-C to quit)…")
    monitor_and_plot(DATA_FILE, POLL_INTERVAL)
