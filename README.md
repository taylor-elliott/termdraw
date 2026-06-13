# draw

- A node/graph sketcher that runs entirely in your terminal

- A **board** holds draw-nodes, and each node opens full-screen as a **canvas** (drawn on a braille sub-cell grid for 8× the resolution of text)

- Pure Python standard library, no dependencies

## Run

```bash
python3 draw.py              # open the board
python3 draw.py myboard      # set the default board/file name
python3 draw.py --canvas     # jump straight into a single canvas
python3 draw.py --help       # all options
```

- Works best in a terminal with pixel-level mouse + truecolor (WezTerm, kitty, foot, ghostty, contour)

- Falls back to cell-level mouse elsewhere — including **iTerm2** and Terminal.app, which report a pixel cell size but don't implement SGR-Pixel mouse (`CSI ?1016`). Forcing pixel mode there desyncs the cursor from where you draw, so it's auto-disabled.

- Override the auto-detection with `DRAW_PIXEL_MOUSE=1` (force on) or `DRAW_PIXEL_MOUSE=0` (force off)

> **iTerm2 right-click:** by default iTerm2 binds right-click to its own context menu, so plain right-click never reaches the app. Use `⌘`+right-click, or free up the binding in *Settings → Pointer*. Every menu action also has a key (`d` delete, `r` rename, `l` link, `Enter` open, `n` new node) and in the canvas the `e` eraser tool replaces right-drag.

## Board

- **click** select
- **drag** move
- **Enter** open a node
- **right-click** menu (enter / rename / copy / link / delete, or new node / new board)
- `n` new node
- `N` new board
- `d` delete
- `l` link two nodes (graph edges)
- `r` rename
- `Tab` cycle
- `s` save
- `o` open (board = nodes + edges + drawings, saved as JSON)
- `,` settings
- `` ` `` hide/show the UI bar
- `q` quit (prompts if you have unsaved changes)

## Canvas

- **left-drag** draws
- **right-drag** erases
- tools:
  - `f` freehand
  - `l` line
  - `r` rectangle
  - `i` ellipse
  - `a` arrow
  - `e` eraser
  - `v` select/move
    - drag a box over shapes, then drag the box to move them (multi-select; right-click clears)
- `[` / `]` or scroll-wheel resize the eraser (a ring shows the area)
- `1`–`8` colors
- `u` undo
- `R` redo
- `c` clear
- `x` export the node to **SVG**
- `b`/`Tab`/`q` back to board

## Settings (`,` on the board)

- Toggle features (hover behavior, hint labels, hide UI), set default tool/color/eraser size, choose working/save/open directories, and **remap any key**. Saved to `~/.draw.json`

- Press `?` in either mode for the full, live key reference
