#!/usr/bin/env python3

# Renders the figures of optimizations.md into this directory:
#
#   layout-0.png ... layout-3.png  the running example as each layout compiler lays it
#   layouts.png                    the four layouts at one scale
#   ticks-by-transfer.svg          the ticks of the running example by kind of transfer
#   selfie-ticks.svg               the ticks of selfie compiling itself per layout
#
# Run from the root of the repository, after make selfie riscr cellfie:
#
#   python3 figures/render.py
#
# For each layout the script takes tools/cellfie.c and tools/btor2.h of the
# commit that introduced it, has the event-driven simulator print the ticks
# whenever the token is on the path of an instruction cell, builds it with
# the current selfie.h, and compiles and runs the running example. The ticks
# of selfie are not measured here, make selfie-on-cellfie takes minutes:
# they are the numbers of optimizations.md, to be updated with it.
#
# Needs git, cc, and the Python Imaging Library.

import os
import re
import subprocess
import sys
import tempfile

from PIL import Image, ImageDraw, ImageFont

EXAMPLE = "examples/symbolic/recursive-fibonacci-1-10"
INPUT   = "tests/bitr-input.txt"

# the cells that the layouts of the examples have: 2048 words of history,
# 64 words of heap, 128 words of stack, as in make layouts

MEMORY = ["-heap", "0", "2048", "-heap", "1048576", "64", "-stack", "128", "-i", INPUT]

HISTORY_WORDS = 2048

# label, commit of tools/cellfie.c, ticks of selfie compiling itself

LAYOUTS = [
    ("0. one row",            "cdf037e", 376091754479047372),
    ("1. words in strips",    "78dc61f", 350763823005762),
    ("2. the stack first",    "f5a3cd6", 148280941906994),
    ("3. the path in strips", "5d76d28", 94297978686148),
]

# selfie's instruction identifiers

LOAD  = 9
ECALL = 14

# the palette: a light surface, text in ink, cells and series in fixed order

SURFACE   = "#fcfcfb"
INK       = "#0b0b0b"
INK_2     = "#52514e"
GRID      = "#e6e5e0"
BLUE      = "#2a78d6"
ORANGE    = "#eb6834"
AQUA      = "#1baf7a"
YELLOW    = "#eda100"
MIRROR    = "#9a9992"

KINDS  = ["instruction", "memory", "tape", "router", "mirror"]
COLORS = {"instruction": BLUE, "memory": ORANGE, "tape": AQUA, "router": YELLOW, "mirror": MIRROR}

TRANSFERS = ["stack", "history", "control", "other"]

TRANSFER_NAMES  = {"stack": "stack", "history": "pushes onto the history stack", "control": "control", "other": "data, heap, system calls, next instruction"}
TRANSFER_COLORS = {"stack": BLUE, "history": ORANGE, "control": AQUA, "other": YELLOW}

TRACE = """  while (and(property == PROPERTY_NONE, executed_ticks - start < ticks)) {
    tick();
"""

TRACED = """  while (and(property == PROPERTY_NONE, executed_ticks - start < ticks)) {
    if (get_cell_kind(*(cell_kinds + cell_index(token_x, token_y))) == CELL_INSTRUCTION)
      if (token_heading == EAST)
        if (token_leg == 0) {
          decode_cell(*(cell_words + cell_index(token_x, token_y)));

          printf("@ %lX %lu %lu %lX\\n", token_pc, executed_ticks, is, get_token_register(rs1) + imm);
        }

    tick();
"""


def run(command, stdin=None):
    return subprocess.run(command, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True).stdout.decode(errors="replace")


def show(commit, path):
    return subprocess.run(["git", "show", commit + ":" + path], stdout=subprocess.PIPE, check=True).stdout.decode()


def build(commit, directory):
    # the layout compiler of a commit, tracing

    source = show(commit, "tools/cellfie.c")

    if source.count(TRACE) != 1:
        sys.exit("cannot trace tools/cellfie.c of " + commit)

    with open(os.path.join(directory, "cellfie.c"), "w") as file:
        file.write(source.replace(TRACE, TRACED))

    with open(os.path.join(directory, "btor2.h"), "w") as file:
        file.write(show(commit, "tools/btor2.h"))

    binary = os.path.join(directory, "cellfie")

    run(["cc", "-w", "-O2", "-Duint64_t=unsigned long", "--include", "selfie.h", "--include",
        os.path.join(directory, "btor2.h"), os.path.join(directory, "cellfie.c"), "-o", binary])

    return binary


def read_layout(name):
    # the cells of a layout that are not blank, as (x, y, kind)

    width  = 0
    height = 0

    body = ""

    with open(name) as file:
        for line in file:
            match = re.match(r"x = (\d+), y = (\d+)", line)

            if match:
                width  = int(match.group(1))
                height = int(match.group(2))
            elif not line.startswith("#"):
                body = body + line.strip()

    cells = []

    x = 0
    y = 0

    pattern = r"(\d*)(\.|/|\\|R[/\\][pa]\d\d|[MT][0-9a-f]{16}(?:@[0-9a-f]{16})?|[ENWS][/\\][0-9a-f]{8}(?:@[0-9a-f]{16})?|\$|!)"

    for match in re.finditer(pattern, body):
        count  = int(match.group(1) or 1)
        symbol = match.group(2)[0]

        if symbol == "!":
            break
        elif symbol == "$":
            x = 0
            y = y + count
        else:
            if symbol != ".":
                if symbol in "/\\":
                    kind = "mirror"
                elif symbol == "R":
                    kind = "router"
                elif symbol == "M":
                    kind = "memory"
                elif symbol == "T":
                    kind = "tape"
                else:
                    kind = "instruction"

                for i in range(count):
                    cells.append((x + i, y, kind))

            x = x + count

    return width, height, cells


def read_trace(output, heap_start):
    # the ticks between instructions, by kind of transfer

    steps = []

    for line in output.split("\n"):
        if line.startswith("@ "):
            fields = line.split()

            steps.append((int(fields[1], 16), int(fields[2]), int(fields[3]), int(fields[4], 16)))

    ticks  = dict((transfer, 0) for transfer in TRANSFERS)
    counts = dict((transfer, 0) for transfer in TRANSFERS)

    for i in range(len(steps) - 1):
        pc, tick, instruction, address = steps[i]

        if instruction == LOAD:
            if address >= 0xFFFFF000:
                transfer = "stack"
            elif heap_start <= address < heap_start + HISTORY_WORDS * 8:
                transfer = "history"
            else:
                transfer = "other"
        elif instruction != ECALL and steps[i + 1][0] != pc + 4:
            transfer = "control"
        else:
            transfer = "other"

        ticks[transfer]  = ticks[transfer] + steps[i + 1][1] - tick
        counts[transfer] = counts[transfer] + 1

    return ticks, counts, steps[-1][1], len(steps)


def font(size, bold=False):
    name = "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf"

    for directory in ["/usr/share/fonts/truetype/dejavu/", "/Library/Fonts/", ""]:
        try:
            return ImageFont.truetype(directory + name, size)
        except OSError:
            pass

    return ImageFont.load_default()


def draw_cells(cells, block, scale):
    # an image of the cells in their bounding box: a block of block x block
    # cells is a pixel, or a cell is scale x scale pixels; where cells share
    # a pixel the kind that computes shows

    x0 = min(x for x, y, kind in cells)
    y0 = min(y for x, y, kind in cells)
    x1 = max(x for x, y, kind in cells)
    y1 = max(y for x, y, kind in cells)

    image = Image.new("RGB", (((x1 - x0) // block + 1) * scale, ((y1 - y0) // block + 1) * scale), SURFACE)

    draw = ImageDraw.Draw(image)

    for kind in reversed(KINDS):
        for x, y, k in cells:
            if k == kind:
                px = (x - x0) // block * scale
                py = (y - y0) // block * scale

                draw.rectangle([px, py, px + scale - 1, py + scale - 1], fill=COLORS[kind])

    return image


def legend(draw, x, y, entries, size):
    for name, color in entries:
        draw.rectangle([x, y + 2, x + size - 3, y + size - 1], fill=color)

        draw.text((x + size + 4, y), name, fill=INK_2, font=font(size))

        x = x + size + 4 + int(draw.textlength(name, font=font(size))) + 18


def frame(image, title, subtitle):
    # an image with a title, a subtitle, and the legend of the cells above it

    margin = 16

    width = max(image.width + 2 * margin, 760)

    framed = Image.new("RGB", (width, image.height + 92 + margin), SURFACE)

    draw = ImageDraw.Draw(framed)

    draw.text((margin, 12), title, fill=INK, font=font(16, True))
    draw.text((margin, 36), subtitle, fill=INK_2, font=font(13))

    legend(draw, margin, 62, [(kind, COLORS[kind]) for kind in KINDS], 13)

    framed.paste(image, (margin, 92))

    return framed


def number(n):
    return format(n, ",")


def svg_text(x, y, text, size=12, anchor="start", color=INK_2, weight="normal"):
    return '<text x="%s" y="%s" font-size="%d" text-anchor="%s" fill="%s" font-weight="%s">%s</text>\n' % (x, y, size, anchor, color, weight, text)


def svg_open(width, height):
    return ('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d" font-family="DejaVu Sans, Helvetica, Arial, sans-serif">\n'
        '<rect width="%d" height="%d" fill="%s"/>\n') % (width, height, width, height, width, height, SURFACE)


def render_transfers(results, name):
    # one bar per layout, stacked by kind of transfer, the total at its tip

    left   = 170
    right  = 150
    width  = 900
    top    = 96
    band   = 44
    bar    = 22
    height = top + band * len(results) + 44

    longest = max(total for label, ticks, counts, total, instructions in results)

    limit = 1400000

    while limit - 200000 >= longest:
        limit = limit - 200000

    plot = width - left - right

    svg = svg_open(width, height)

    svg = svg + svg_text(16, 26, "Ticks of the running example by kind of transfer", 16, "start", INK, "bold")
    svg = svg + svg_text(16, 46, "fibonacci(3), %s RISC-R instructions, on the layout of each layout compiler" % number(results[0][4]), 13)

    x = 16

    for transfer in TRANSFERS:
        svg = svg + '<rect x="%d" y="62" width="11" height="11" fill="%s"/>\n' % (x, TRANSFER_COLORS[transfer])
        svg = svg + svg_text(x + 16, 72, TRANSFER_NAMES[transfer], 12)

        x = x + 16 + int(len(TRANSFER_NAMES[transfer]) * 6.9) + 18

    tick = 0

    while tick <= limit:
        gx = left + plot * tick / limit

        svg = svg + '<line x1="%.1f" y1="%d" x2="%.1f" y2="%d" stroke="%s" stroke-width="1"/>\n' % (gx, top - 6, gx, top + band * len(results), GRID)
        svg = svg + svg_text("%.1f" % gx, top + band * len(results) + 18, number(tick), 11, "middle")

        tick = tick + 200000

    svg = svg + svg_text(left + plot / 2, top + band * len(results) + 36, "ticks", 11, "middle")

    for i in range(len(results)):
        label, ticks, counts, total, instructions = results[i]

        y = top + band * i + (band - bar) / 2

        svg = svg + svg_text(left - 10, y + bar / 2 + 4, label, 12, "end", INK)

        x = left

        for transfer in TRANSFERS:
            w = plot * ticks[transfer] / limit

            if w > 2:
                # a gap in the colour of the surface separates the segments

                svg = svg + '<rect x="%.1f" y="%.1f" width="%.1f" height="%d" fill="%s"><title>%s: %s ticks in %d transfers</title></rect>\n' % (
                    x, y, w - 2, bar, TRANSFER_COLORS[transfer], TRANSFER_NAMES[transfer], number(ticks[transfer]), counts[transfer])

            x = x + w

        svg = svg + svg_text("%.1f" % (x + 6), y + bar / 2 + 4, number(total), 12, "start", INK)

    svg = svg + "</svg>\n"

    with open(name, "w") as file:
        file.write(svg)


def render_selfie(name):
    # one dot per layout on a logarithmic axis: the ticks of selfie compiling itself

    import math

    left   = 170
    right  = 250
    width  = 900
    top    = 70
    band   = 40
    height = top + band * len(LAYOUTS) + 44

    lo = 13
    hi = 18

    plot = width - left - right

    svg = svg_open(width, height)

    svg = svg + svg_text(16, 26, "Ticks of selfie compiling itself", 16, "start", INK, "bold")
    svg = svg + svg_text(16, 46, "1,388,403,685 RISC-R instructions on the layout of each layout compiler, logarithmic scale", 13)

    for exponent in range(lo, hi + 1):
        gx = left + plot * (exponent - lo) / (hi - lo)

        svg = svg + '<line x1="%.1f" y1="%d" x2="%.1f" y2="%d" stroke="%s" stroke-width="1"/>\n' % (gx, top - 6, gx, top + band * len(LAYOUTS), GRID)
        svg = svg + svg_text("%.1f" % gx, top + band * len(LAYOUTS) + 18, "10^%d" % exponent, 11, "middle")

    svg = svg + svg_text(left + plot / 2, top + band * len(LAYOUTS) + 36, "ticks", 11, "middle")

    for i in range(len(LAYOUTS)):
        label, commit, ticks = LAYOUTS[i]

        y = top + band * i + band / 2

        gx = left + plot * (math.log10(ticks) - lo) / (hi - lo)

        svg = svg + svg_text(left - 10, y + 4, label, 12, "end", INK)

        svg = svg + '<circle cx="%.1f" cy="%.1f" r="6" fill="%s" stroke="%s" stroke-width="2"><title>%s ticks</title></circle>\n' % (gx, y, BLUE, SURFACE, number(ticks))

        text = "%.3g" % ticks

        text = text.replace("e+", " x 10^")

        if i > 0:
            text = text + ", %s times fewer" % number(round(LAYOUTS[i - 1][2] / ticks, 2) if LAYOUTS[i - 1][2] / ticks < 100 else round(LAYOUTS[i - 1][2] / ticks))

        svg = svg + svg_text("%.1f" % (gx + 14), y + 4, text, 12, "start", INK)

    svg = svg + "</svg>\n"

    with open(name, "w") as file:
        file.write(svg)


def main():
    out = os.path.dirname(os.path.abspath(__file__))

    results = []
    layouts = []

    with tempfile.TemporaryDirectory() as directory:
        # the name of the binary is on its stack: as make layouts names it

        binary  = EXAMPLE + ".m"
        rbinary = EXAMPLE + ".r"

        run(["./selfie", "-c", EXAMPLE + ".c", "-o", binary])
        run(["./riscr", "-l", binary, "-history", "1", "-t", rbinary])

        for label, commit, selfie_ticks in LAYOUTS:
            work = os.path.join(directory, commit)

            os.mkdir(work)

            cellfie = build(commit, work)

            layout = os.path.join(work, "fib.rle")

            output = run([cellfie] + MEMORY + ["-c", rbinary, "-o", layout, "-f", "100000000"])

            width, height, cells = read_layout(layout)

            # the heap begins at the program break in the layout

            heap_start = 0

            with open(layout) as file:
                for line in file:
                    if line.startswith("#S "):
                        heap_start = int(line.split()[1], 16)

            ticks, counts, total, instructions = read_trace(output, heap_start)

            # the simulator counts the ticks into the exit as well

            total = int(re.search(r"after (\d+) ticks and (\d+) instructions", output).group(1))

            ticks["other"] = total - ticks["stack"] - ticks["history"] - ticks["control"]

            results.append((label, ticks, counts, total, instructions))
            layouts.append((label, width, height, cells, total))

            print("%s: %dx%d, %d cells, %d ticks, %s" % (label, width, height, len(cells), total,
                ", ".join("%s %d in %d" % (t, ticks[t], counts[t]) for t in TRANSFERS)))

    # each layout as large as it fits

    for i in range(len(layouts)):
        label, width, height, cells, total = layouts[i]

        span = max(x for x, y, kind in cells) - min(x for x, y, kind in cells) + 1

        block = max(1, -(-span // 1400))
        scale = max(1, min(3, 1400 // span))

        image = draw_cells(cells, block, scale)

        if block > 1:
            unit = "one pixel is %d x %d cells" % (block, block)
        else:
            unit = "one cell is %d x %d pixels" % (scale, scale)

        frame(image, "Layout " + label, "fibonacci(3) on a grid of %d x %d cells, %s cells that are not blank, %s ticks; %s" % (
            width, height, number(len(cells)), number(total), unit)).save(os.path.join(out, "layout-%d.png" % i))

    # all layouts at one scale: a pixel is 3 x 3 cells

    images = [draw_cells(cells, 3, 1) for label, width, height, cells, total in layouts]

    margin = 16
    gap    = 28

    row = sum(max(image.width, 190) for image in images[1:]) + gap * (len(images) - 2)

    width  = max(images[0].width, row) + 2 * margin
    height = 92 + 22 + images[0].height + gap + 22 + max(image.height for image in images[1:]) + margin

    overview = Image.new("RGB", (width, height), SURFACE)

    draw = ImageDraw.Draw(overview)

    draw.text((margin, 12), "The four layouts of the running example at one scale", fill=INK, font=font(16, True))
    draw.text((margin, 36), "one pixel is 3 x 3 cells; only the part of each grid that has cells", fill=INK_2, font=font(13))

    legend(draw, margin, 62, [(kind, COLORS[kind]) for kind in KINDS], 13)

    y = 92

    draw.text((margin, y), "%s: %s ticks" % (layouts[0][0], number(layouts[0][4])), fill=INK, font=font(12))

    overview.paste(images[0], (margin, y + 22))

    y = y + 22 + images[0].height + gap

    x = margin

    for i in range(1, len(images)):
        draw.text((x, y), "%s: %s" % (layouts[i][0], number(layouts[i][4])), fill=INK, font=font(12))

        overview.paste(images[i], (x, y + 22))

        x = x + max(images[i].width, 190) + gap

    overview.save(os.path.join(out, "layouts.png"))

    render_transfers(results, os.path.join(out, "ticks-by-transfer.svg"))

    render_selfie(os.path.join(out, "selfie-ticks.svg"))


main()
