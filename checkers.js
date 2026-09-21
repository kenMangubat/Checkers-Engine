(() => {
    const SIZE = 8;
    const DIRS = [
        [-1, -1],
        [-1, 1],
        [1, -1],
        [1, 1],
    ];

    const boardEl = document.getElementById("board");
    const statusEl = document.getElementById("status");
    const hintEl = document.getElementById("hint");
    const engineEl = document.getElementById("engine-line");
    const modeEl = document.getElementById("mode");
    const depthEl = document.getElementById("depth");
    const rulesDialog = document.getElementById("rules-dialog");

    let board;
    let turn;
    let history;
    let posCounts;
    let selected;
    let prefix;
    let legal;
    let over;
    let aiBusy;

    function inBounds(r, c) {
        return r >= 0 && r < SIZE && c >= 0 && c < SIZE;
    }

    function playable(r, c) {
        return (r + c) % 2 === 1;
    }

    function cloneBoard(src) {
        return src.map((row) => row.map((p) => (p ? { color: p.color, king: p.king } : null)));
    }

    function empty(b, r, c) {
        return inBounds(r, c) && b[r][c] === null;
    }

    function opponent(color) {
        return color === "w" ? "b" : "w";
    }

    function forwardDirs(color) {
        return color === "w" ? [[-1, -1], [-1, 1]] : [[1, -1], [1, 1]];
    }

    function promoteRank(color) {
        return color === "w" ? 0 : SIZE - 1;
    }

    function capKey(r, c) {
        return r + "," + c;
    }

    function newBoard() {
        const b = Array.from({ length: SIZE }, () => Array(SIZE).fill(null));
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                if (!playable(r, c)) continue;
                if (r <= 2) b[r][c] = { color: "b", king: false };
                if (r >= 5) b[r][c] = { color: "w", king: false };
            }
        }
        return b;
    }

    function manCaptures(b, r, c, color, captured) {
        const sequences = [];

        function walk(cr, cc, caps, path) {
            let branched = false;
            for (const [dr, dc] of DIRS) {
                const vr = cr + dr;
                const vc = cc + dc;
                const lr = cr + 2 * dr;
                const lc = cc + 2 * dc;
                if (!empty(b, lr, lc)) continue;
                const vic = inBounds(vr, vc) ? b[vr][vc] : null;
                if (!vic || vic.color === color) continue;
                const key = capKey(vr, vc);
                if (caps.has(key)) continue;
                branched = true;
                const nextCaps = new Set(caps);
                nextCaps.add(key);
                walk(lr, lc, nextCaps, path.concat([{ r: lr, c: lc, victims: [[vr, vc]] }]));
            }
            if (!branched && path.length) sequences.push({ path, captured: [...caps] });
        }

        walk(r, c, captured, []);
        return sequences;
    }

    function kingCaptures(b, r, c, color, captured) {
        const sequences = [];

        function walk(cr, cc, caps, path) {
            let branched = false;
            for (const [dr, dc] of DIRS) {
                let vr = cr + dr;
                let vc = cc + dc;
                while (inBounds(vr, vc) && empty(b, vr, vc)) {
                    vr += dr;
                    vc += dc;
                }
                if (!inBounds(vr, vc)) continue;
                const vic = b[vr][vc];
                if (!vic || vic.color === color) continue;
                const key = capKey(vr, vc);
                if (caps.has(key)) continue;
                let lr = vr + dr;
                let lc = vc + dc;
                while (inBounds(lr, lc) && empty(b, lr, lc)) {
                    branched = true;
                    const nextCaps = new Set(caps);
                    nextCaps.add(key);
                    walk(lr, lc, nextCaps, path.concat([{ r: lr, c: lc, victims: [[vr, vc]] }]));
                    lr += dr;
                    lc += dc;
                }
            }
            if (!branched && path.length) sequences.push({ path, captured: [...caps] });
        }

        walk(r, c, captured, []);
        return sequences;
    }

    function quietMoves(b, r, c, piece) {
        const moves = [];
        const dirs = piece.king ? DIRS : forwardDirs(piece.color);
        for (const [dr, dc] of dirs) {
            if (piece.king) {
                let nr = r + dr;
                let nc = c + dc;
                while (empty(b, nr, nc)) {
                    moves.push({
                        from: [r, c],
                        path: [{ r: nr, c: nc, victims: [] }],
                        captured: [],
                    });
                    nr += dr;
                    nc += dc;
                }
            } else if (empty(b, r + dr, c + dc)) {
                moves.push({
                    from: [r, c],
                    path: [{ r: r + dr, c: c + dc, victims: [] }],
                    captured: [],
                });
            }
        }
        return moves;
    }

    function allMoves(b, color) {
        const captures = [];
        const quiets = [];
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                const p = b[r][c];
                if (!p || p.color !== color) continue;
                const seqs = p.king
                    ? kingCaptures(b, r, c, color, new Set())
                    : manCaptures(b, r, c, color, new Set());
                for (const s of seqs) {
                    captures.push({ from: [r, c], path: s.path, captured: s.captured });
                }
                quiets.push(...quietMoves(b, r, c, p));
            }
        }
        if (!captures.length) return quiets;
        const maxN = Math.max(...captures.map((m) => m.captured.length));
        return captures.filter((m) => m.captured.length === maxN);
    }

    function applyMove(b, move) {
        const next = cloneBoard(b);
        const [fr, fc] = move.from;
        const piece = { color: next[fr][fc].color, king: next[fr][fc].king };
        next[fr][fc] = null;
        for (const step of move.path) {
            for (const [vr, vc] of step.victims) next[vr][vc] = null;
        }
        const last = move.path[move.path.length - 1];
        if (!piece.king && last.r === promoteRank(piece.color)) piece.king = true;
        next[last.r][last.c] = piece;
        return next;
    }

    function countPieces(b) {
        const n = { w: 0, b: 0, wk: 0, bk: 0, wm: 0, bm: 0 };
        for (const row of b) {
            for (const p of row) {
                if (!p) continue;
                n[p.color] += 1;
                if (p.king) n[p.color + "k"] += 1;
                else n[p.color + "m"] += 1;
            }
        }
        return n;
    }

    function posKey(b, side) {
        let s = side;
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                const p = b[r][c];
                s += !p ? "." : p.color === "w" ? (p.king ? "W" : "w") : p.king ? "B" : "b";
            }
        }
        return s;
    }

    function kingEndgameDraw(n) {
        if (n.wm || n.bm) return false;
        const hi = Math.max(n.wk, n.bk);
        const lo = Math.min(n.wk, n.bk);
        return lo === 1 && hi >= 1 && hi <= 3;
    }

    function resultOf(b, side, counts) {
        const moves = allMoves(b, side);
        const n = countPieces(b);
        if (n[side] === 0 || moves.length === 0) {
            return { over: true, draw: false, winner: opponent(side) };
        }
        if (kingEndgameDraw(n)) return { over: true, draw: true, winner: null };
        if ((counts[posKey(b, side)] || 0) >= 3) return { over: true, draw: true, winner: null };
        return { over: false };
    }

    function matchingMoves() {
        if (!selected) return [];
        return legal.filter((m) => {
            if (m.from[0] !== selected[0] || m.from[1] !== selected[1]) return false;
            return prefix.every((step, i) => m.path[i] && m.path[i].r === step.r && m.path[i].c === step.c);
        });
    }

    function viewBoard() {
        const b = cloneBoard(board);
        const moves = matchingMoves();
        if (!selected || !prefix.length || !moves.length) return b;
        const [fr, fc] = selected;
        if (!b[fr][fc]) return b;
        const piece = { ...b[fr][fc] };
        b[fr][fc] = null;
        const sample = moves[0];
        for (let i = 0; i < prefix.length; i++) {
            for (const [vr, vc] of sample.path[i].victims) b[vr][vc] = null;
        }
        const last = prefix[prefix.length - 1];
        b[last.r][last.c] = piece;
        return b;
    }

    function playMove(move) {
        board = applyMove(board, move);
        history.push({ move, beforeTurn: opponent(turn) });
        turn = opponent(turn);
        selected = null;
        prefix = [];
        const key = posKey(board, turn);
        posCounts[key] = (posCounts[key] || 0) + 1;
        legal = allMoves(board, turn);
        over = resultOf(board, turn, posCounts);
        if (over.over) legal = [];
        render();
        if (!over.over) maybeAi();
    }

    function squareClick(r, c) {
        if (over?.over || aiBusy) return;
        if (modeEl.value === "ai" && turn === "b") return;

        if (!selected && board[r][c]?.color === turn && legal.some((m) => m.from[0] === r && m.from[1] === c)) {
            selected = [r, c];
            prefix = [];
            render();
            return;
        }

        const destMoves = matchingMoves().filter((m) => {
            const step = m.path[prefix.length];
            return step && step.r === r && step.c === c;
        });

        if (destMoves.length) {
            if (!selected) selected = destMoves[0].from.slice();
            prefix = prefix.concat([{ r, c }]);
            const left = matchingMoves();
            const complete = left.filter((m) => m.path.length === prefix.length);
            const longer = left.filter((m) => m.path.length > prefix.length);
            if (longer.length === 0 && complete.length) {
                playMove(complete[0]);
                return;
            }
            render();
            return;
        }

        if (prefix.length) return;

        const p = board[r][c];
        if (!p || p.color !== turn || !legal.some((m) => m.from[0] === r && m.from[1] === c)) {
            selected = null;
            prefix = [];
            render();
            return;
        }
        selected = [r, c];
        prefix = [];
        render();
    }

    function undo() {
        if (aiBusy || !history.length) return;
        const plies = modeEl.value === "ai" && history.length >= 2 ? 2 : 1;
        for (let i = 0; i < plies; i++) {
            history.pop();
        }
        rebuildFromHistory();
        render();
    }

    function rebuildFromHistory() {
        board = newBoard();
        turn = "w";
        posCounts = { [posKey(board, turn)]: 1 };
        for (const rec of history) {
            board = applyMove(board, rec.move);
            turn = opponent(turn);
            const key = posKey(board, turn);
            posCounts[key] = (posCounts[key] || 0) + 1;
        }
        selected = null;
        prefix = [];
        over = resultOf(board, turn, posCounts);
        legal = over.over ? [] : allMoves(board, turn);
    }

    function evalBoard(b, color) {
        const n = countPieces(b);
        let score = (n.w - n.b) * 100 + (n.wk - n.bk) * 170;
        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                const p = b[r][c];
                if (!p) continue;
                const s = p.color === "w" ? 1 : -1;
                if (!p.king) score += s * (p.color === "w" ? SIZE - 1 - r : r) * 4;
                else score += s * (4 - Math.abs(r - 3.5) - Math.abs(c - 3.5));
                if (r > 1 && r < 6 && c > 1 && c < 6) score += 3 * s;
            }
        }
        score += (allMoves(b, "w").length - allMoves(b, "b").length) * 2;
        return color === "w" ? score : -score;
    }

    function search(b, color, depth, alpha, beta) {
        const moves = allMoves(b, color);
        const n = countPieces(b);
        if (n[color] === 0 || moves.length === 0) return { score: -100000 + depth };
        if (kingEndgameDraw(n)) return { score: 0 };
        if (depth === 0) return { score: evalBoard(b, color) };

        let best = { score: -Infinity, move: moves[0] };
        for (const mv of moves) {
            const child = search(applyMove(b, mv), opponent(color), depth - 1, -beta, -alpha);
            const score = -child.score;
            if (score > best.score) best = { score, move: mv };
            if (score > alpha) alpha = score;
            if (alpha >= beta) break;
        }
        return best;
    }

    function maybeAi() {
        if (over?.over || modeEl.value !== "ai" || turn !== "b") return;
        aiBusy = true;
        engineEl.textContent = "Engine thinking…";
        render();
        const depth = Number(depthEl.value);
        const snapshot = cloneBoard(board);
        const side = turn;
        setTimeout(() => {
            const { move, score } = search(snapshot, side, depth, -Infinity, Infinity);
            aiBusy = false;
            if (!move) {
                over = resultOf(board, turn, posCounts);
                render();
                return;
            }
            engineEl.textContent = "Engine eval " + (score / 100).toFixed(2);
            playMove(move);
        }, 30);
    }

    function hintMove() {
        if (over?.over || aiBusy) return;
        const depth = Math.min(4, Number(depthEl.value));
        const { move } = search(cloneBoard(board), turn, depth, -Infinity, Infinity);
        if (!move) return;
        selected = move.from.slice();
        prefix = [];
        hintEl.textContent =
            "Hint: " + sqName(move.from[0], move.from[1]) + " → " + sqName(move.path.at(-1).r, move.path.at(-1).c);
        render(move);
    }

    function sqName(r, c) {
        return "abcdefgh"[c] + (8 - r);
    }

    function render(hintOnly) {
        const shown = viewBoard();
        boardEl.innerHTML = "";
        const destSet = new Set();
        const originSet = new Set();
        const jumpSet = new Set();
        const pool = hintOnly ? [hintOnly] : selected ? matchingMoves() : [];
        if (!selected && !hintOnly && legal[0]?.captured.length) {
            for (const m of legal) originSet.add(capKey(m.from[0], m.from[1]));
        }
        for (const m of pool) {
            originSet.add(capKey(m.from[0], m.from[1]));
            const step = m.path[prefix.length];
            if (step) destSet.add(capKey(step.r, step.c));
            if (selected) {
                for (const part of m.path) {
                    for (const [vr, vc] of part.victims) jumpSet.add(capKey(vr, vc));
                }
            }
        }

        for (let r = 0; r < SIZE; r++) {
            for (let c = 0; c < SIZE; c++) {
                const sq = document.createElement("div");
                sq.className = "sq " + ((r + c) % 2 === 0 ? "light" : "dark");
                const k = capKey(r, c);
                if (originSet.has(k) && prefix.length === 0) sq.classList.add("origin");
                if (destSet.has(k)) sq.classList.add("dest");
                if (jumpSet.has(k)) sq.classList.add("jump");
                if (c === 0) {
                    const rank = document.createElement("span");
                    rank.className = "coord rank";
                    rank.textContent = String(8 - r);
                    sq.appendChild(rank);
                }
                if (r === SIZE - 1) {
                    const file = document.createElement("span");
                    file.className = "coord file";
                    file.textContent = "abcdefgh"[c];
                    sq.appendChild(file);
                }
                const p = shown[r][c];
                if (p) {
                    const el = document.createElement("div");
                    const isSel =
                        (prefix.length === 0 && selected && selected[0] === r && selected[1] === c) ||
                        (prefix.length && prefix[prefix.length - 1].r === r && prefix[prefix.length - 1].c === c);
                    el.className = "piece " + p.color + (p.king ? " king" : "") + (isSel ? " selected" : "");
                    sq.appendChild(el);
                }
                sq.addEventListener("click", () => squareClick(r, c));
                boardEl.appendChild(sq);
            }
        }

        const n = countPieces(board);
        document.getElementById("count-white").textContent = String(n.w);
        document.getElementById("count-black").textContent = String(n.b);
        document.getElementById("count-reps").textContent = (posCounts[posKey(board, turn)] || 1) + " / 3";
        renderCaptures(n);

        if (over?.over) {
            statusEl.classList.add("over");
            statusEl.textContent = over.draw ? "Draw" : (over.winner === "w" ? "White" : "Black") + " wins";
            hintEl.textContent = over.draw
                ? "Threefold repetition or king endgame (1 vs 1–3 kings)."
                : "All pieces captured or no legal moves.";
            return;
        }
        statusEl.classList.remove("over");
        statusEl.textContent = (turn === "w" ? "White" : "Black") + (aiBusy ? " (thinking)" : " to move");
        if (hintOnly) return;
        const capN = legal[0]?.captured.length || 0;
        hintEl.textContent = prefix.length
            ? "Continue the capture. The longest sequence is required."
            : capN
                ? "Mandatory capture of " + capN + " piece" + (capN > 1 ? "s" : "") + "."
                : "";
    }

    function renderCaptures(n) {
        const whiteTray = document.getElementById("captured-by-white");
        const blackTray = document.getElementById("captured-by-black");
        whiteTray.innerHTML = "";
        blackTray.innerHTML = "";
        for (let i = 0; i < 12 - n.b; i++) whiteTray.appendChild(mini("b"));
        for (let i = 0; i < 12 - n.w; i++) blackTray.appendChild(mini("w"));
    }

    function mini(color) {
        const el = document.createElement("span");
        el.className = "mini " + color;
        return el;
    }

    function reset() {
        board = newBoard();
        turn = "w";
        history = [];
        selected = null;
        prefix = [];
        over = null;
        aiBusy = false;
        posCounts = { [posKey(board, turn)]: 1 };
        legal = allMoves(board, turn);
        engineEl.textContent = "Engine idle";
        render();
    }

    document.getElementById("btn-new").addEventListener("click", reset);
    document.getElementById("btn-undo").addEventListener("click", undo);
    document.getElementById("btn-hint").addEventListener("click", hintMove);
    document.getElementById("btn-rules").addEventListener("click", () => rulesDialog.showModal());
    modeEl.addEventListener("change", reset);

    reset();

    reset();
})();
