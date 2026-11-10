(() => {
  "use strict";

  const TOTAL_LEVELS = 100;
  const STORAGE_KEY = "sudoku_completed_levels";

  /* ---------- Helpers ---------- */
  const $ = (sel) => document.querySelector(sel);

  function tierOf(level) {
    if (level <= 25) return { key: "easy", name: "Easy" };
    if (level <= 50) return { key: "medium", name: "Medium" };
    if (level <= 75) return { key: "hard", name: "Hard" };
    return { key: "expert", name: "Expert" };
  }

  // Number of given clues: level 1 -> 46 clues, level 100 -> 24 clues
  function clueCount(level) {
    return Math.round(46 - ((level - 1) * 22) / 99);
  }

  function loadCompleted() {
    try {
      return new Set(JSON.parse(localStorage.getItem(STORAGE_KEY)) || []);
    } catch (e) {
      return new Set();
    }
  }
  function saveCompleted(set) {
    try {
      localStorage.setItem(STORAGE_KEY, JSON.stringify([...set]));
    } catch (e) { /* ignore */ }
  }

  /* ---------- Seeded random (same level = same puzzle) ---------- */
  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a = (a + 0x6d2b79f5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }

  function shuffle(arr, rng) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  /* ---------- Puzzle generation ---------- */
  function generateSolution(rng) {
    const base = [];
    for (let r = 0; r < 9; r++) {
      for (let c = 0; c < 9; c++) {
        base.push((r * 3 + Math.floor(r / 3) + c) % 9);
      }
    }
    const digits = shuffle([1, 2, 3, 4, 5, 6, 7, 8, 9], rng);

    const groupOrder = () => {
      const bands = shuffle([0, 1, 2], rng);
      const order = [];
      bands.forEach((b) => {
        shuffle([0, 1, 2], rng).forEach((i) => order.push(b * 3 + i));
      });
      return order;
    };
    const rowOrder = groupOrder();
    const colOrder = groupOrder();

    const grid = new Array(81);
    for (let r = 0; r < 9; r++) {
      for (let c = 0; c < 9; c++) {
        grid[r * 9 + c] = digits[base[rowOrder[r] * 9 + colOrder[c]]];
      }
    }
    return grid;
  }

  function popcount(n) {
    let c = 0;
    while (n) { n &= n - 1; c++; }
    return c;
  }

  // Counts solutions (stops at `limit`)
  function countSolutions(source, limit) {
    const grid = source.slice();
    const rows = new Array(9).fill(0);
    const cols = new Array(9).fill(0);
    const boxes = new Array(9).fill(0);
    let count = 0;

    for (let i = 0; i < 81; i++) {
      const v = grid[i];
      if (v) {
        const bit = 1 << v;
        rows[Math.floor(i / 9)] |= bit;
        cols[i % 9] |= bit;
        boxes[Math.floor(i / 27) * 3 + Math.floor((i % 9) / 3)] |= bit;
      }
    }

    function solve() {
      let best = -1, bestMask = 0, bestCnt = 10;
      for (let i = 0; i < 81; i++) {
        if (grid[i]) continue;
        const r = Math.floor(i / 9), c = i % 9;
        const b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
        const mask = ~(rows[r] | cols[c] | boxes[b]) & 0x3fe;
        const cnt = popcount(mask);
        if (cnt === 0) return;
        if (cnt < bestCnt) {
          best = i; bestMask = mask; bestCnt = cnt;
          if (cnt === 1) break;
        }
      }
      if (best === -1) { count++; return; }

      const r = Math.floor(best / 9), c = best % 9;
      const b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
      for (let n = 1; n <= 9; n++) {
        const bit = 1 << n;
        if (!(bestMask & bit)) continue;
        grid[best] = n;
        rows[r] |= bit; cols[c] |= bit; boxes[b] |= bit;
        solve();
        grid[best] = 0;
        rows[r] &= ~bit; cols[c] &= ~bit; boxes[b] &= ~bit;
        if (count >= limit) return;
      }
    }

    solve();
    return count;
  }

  const puzzleCache = {};

  function buildLevel(level) {
    if (puzzleCache[level]) return puzzleCache[level];

    const rng = mulberry32(level * 7919 + 13);
    const solution = generateSolution(rng);
    const puzzle = solution.slice();
    const target = clueCount(level);
    const order = shuffle([...Array(81).keys()], rng);

    let remaining = 81;
    const deadline = performance.now() + 2000; // safety cap

    for (const idx of order) {
      if (remaining <= target) break;
      if (performance.now() > deadline) break;
      const backup = puzzle[idx];
      puzzle[idx] = 0;
      if (countSolutions(puzzle, 2) !== 1) {
        puzzle[idx] = backup; // removal would break uniqueness
      } else {
        remaining--;
      }
    }

    puzzleCache[level] = { puzzle, solution };
    return puzzleCache[level];
  }

  /* ---------- State ---------- */
  const state = {
    level: 1,
    puzzle: [],
    solution: [],
    user: [],       // current values (given + user entries)
    given: [],      // boolean
    selected: -1,
    wrong: new Set(),
    timerId: null,
    seconds: 0,
    redirectId: null,
    completed: loadCompleted(),
    filter: "all",
  };

  /* ---------- Elements ---------- */
  const homeView = $("#home");
  const gameView = $("#game");
  const levelsEl = $("#levels");
  const progressEl = $("#progress");
  const tabsEl = $("#tabs");
  const boardEl = $("#board");
  const padEl = $("#pad");
  const msgEl = $("#message");
  const checkBtn = $("#checkBtn");
  const submitBtn = $("#submitBtn");
  const levelTitle = $("#levelTitle");
  const levelTier = $("#levelTier");
  const timerEl = $("#timer");
  const modal = $("#modal");
  const modalTitle = $("#modalTitle");
  const modalText = $("#modalText");
  const modalBtn = $("#modalBtn");

  /* ---------- Home ---------- */
  function renderHome() {
    levelsEl.innerHTML = "";
    let shown = 0;
    for (let l = 1; l <= TOTAL_LEVELS; l++) {
      const t = tierOf(l);
      if (state.filter !== "all" && state.filter !== t.key) continue;
      const btn = document.createElement("button");
      btn.className = "level-btn " + t.key + (state.completed.has(l) ? " done" : "");
      btn.textContent = l;
      btn.setAttribute("aria-label", "Level " + l + " " + t.name);
      btn.addEventListener("click", () => startLevel(l));
      levelsEl.appendChild(btn);
      shown++;
    }
    progressEl.textContent =
      "Completed " + state.completed.size + " / " + TOTAL_LEVELS + " levels";
  }

  tabsEl.addEventListener("click", (e) => {
    const tab = e.target.closest(".tab");
    if (!tab) return;
    state.filter = tab.dataset.filter;
    tabsEl.querySelectorAll(".tab").forEach((t) => t.classList.toggle("active", t === tab));
    renderHome();
  });

  function showHome() {
    stopTimer();
    clearTimeout(state.redirectId);
    hideModal();
    gameView.classList.add("hidden");
    homeView.classList.remove("hidden");
    renderHome();
    window.scrollTo(0, 0);
  }

  /* ---------- Game ---------- */
  function buildBoard() {
    boardEl.innerHTML = "";
    for (let i = 0; i < 81; i++) {
      const r = Math.floor(i / 9), c = i % 9;
      const cell = document.createElement("div");
      cell.className = "cell";
      if (r === 2 || r === 5) cell.classList.add("bottom-thick");
      if (c === 2 || c === 5) cell.classList.add("right-thick");
      cell.dataset.i = i;
      cell.setAttribute("role", "gridcell");
      boardEl.appendChild(cell);
    }
  }

  function buildPad() {
    padEl.innerHTML = "";
    for (let n = 1; n <= 9; n++) {
      const b = document.createElement("button");
      b.textContent = n;
      b.addEventListener("click", () => enterValue(n));
      padEl.appendChild(b);
    }
    const erase = document.createElement("button");
    erase.textContent = "Erase";
    erase.className = "erase";
    erase.addEventListener("click", () => enterValue(0));
    padEl.appendChild(erase);
  }

  function startLevel(level) {
    homeView.classList.add("hidden");
    gameView.classList.remove("hidden");
    setMessage("Generating puzzle...", "");
    levelTitle.textContent = "Level " + level;

    // let the browser paint before heavy work
    setTimeout(() => {
      const { puzzle, solution } = buildLevel(level);
      const t = tierOf(level);

      state.level = level;
      state.puzzle = puzzle;
      state.solution = solution;
      state.user = puzzle.slice();
      state.given = puzzle.map((v) => v !== 0);
      state.selected = -1;
      state.wrong = new Set();

      levelTier.textContent = t.name;
      setMessage("", "");
      buildBoard();
      render();
      startTimer();
      window.scrollTo(0, 0);
    }, 30);
  }

  function render() {
    const cells = boardEl.children;
    const sel = state.selected;
    const selVal = sel >= 0 ? state.user[sel] : 0;
    const sr = Math.floor(sel / 9), sc = sel % 9;
    const sb = Math.floor(sr / 3) * 3 + Math.floor(sc / 3);

    for (let i = 0; i < 81; i++) {
      const cell = cells[i];
      const v = state.user[i];
      cell.textContent = v || "";
      cell.classList.toggle("given", state.given[i]);
      cell.classList.toggle("wrong", state.wrong.has(i));
      cell.classList.toggle("selected", i === sel);

      let peer = false, same = false;
      if (sel >= 0 && i !== sel) {
        const r = Math.floor(i / 9), c = i % 9;
        const b = Math.floor(r / 3) * 3 + Math.floor(c / 3);
        peer = r === sr || c === sc || b === sb;
        same = selVal !== 0 && v === selVal;
      }
      cell.classList.toggle("peer", peer && !same);
      cell.classList.toggle("same", same);
    }

    // Submit button visible only when every box is filled
    const allFilled = state.user.every((v) => v !== 0);
    submitBtn.classList.toggle("hidden", !allFilled);
  }

  boardEl.addEventListener("click", (e) => {
    const cell = e.target.closest(".cell");
    if (!cell) return;
    state.selected = Number(cell.dataset.i);
    render();
  });

  function enterValue(n) {
    const i = state.selected;
    if (i < 0 || state.given[i]) return;
    state.user[i] = n;
    state.wrong.delete(i); // editing a cell clears its red highlight
    setMessage("", "");
    render();
  }

  document.addEventListener("keydown", (e) => {
    if (gameView.classList.contains("hidden") || !modal.classList.contains("hidden")) return;

    if (e.key >= "1" && e.key <= "9") {
      enterValue(Number(e.key));
    } else if (e.key === "Backspace" || e.key === "Delete" || e.key === "0") {
      enterValue(0);
    } else if (e.key.startsWith("Arrow")) {
      e.preventDefault();
      let i = state.selected < 0 ? 0 : state.selected;
      const r = Math.floor(i / 9), c = i % 9;
      if (e.key === "ArrowUp" && r > 0) i -= 9;
      if (e.key === "ArrowDown" && r < 8) i += 9;
      if (e.key === "ArrowLeft" && c > 0) i -= 1;
      if (e.key === "ArrowRight" && c < 8) i += 1;
      state.selected = i;
      render();
    }
  });

  /* ---------- Check / Submit ---------- */
  checkBtn.addEventListener("click", () => {
    state.wrong = new Set();
    let filled = 0;
    for (let i = 0; i < 81; i++) {
      if (state.given[i]) continue;
      const v = state.user[i];
      if (v !== 0) {
        filled++;
        if (v !== state.solution[i]) state.wrong.add(i);
      }
    }
    render();

    if (state.wrong.size > 0) {
      setMessage(
        state.wrong.size + (state.wrong.size === 1 ? " box is" : " boxes are") + " wrong.",
        "bad"
      );
    } else if (filled === 0) {
      setMessage("Nothing to check yet.", "");
    } else {
      setMessage("All filled boxes are correct so far!", "good");
    }
  });

  submitBtn.addEventListener("click", () => {
    const correct = state.user.every((v, i) => v === state.solution[i]);
    if (!correct) {
      setMessage("Incorrect solution. Keep trying, KK Anand!", "bad");
      return;
    }

    stopTimer();
    state.completed.add(state.level);
    saveCompleted(state.completed);

    showModal(
      "Well done, KK Anand! 🎉",
      "Level " + state.level + " solved in " + formatTime(state.seconds) +
        ". Taking you back home...",
      "Go home now"
    );
    state.redirectId = setTimeout(showHome, 3000);
  });

  /* ---------- UI utils ---------- */
  function setMessage(text, kind) {
    msgEl.textContent = text;
    msgEl.className = "message" + (kind ? " " + kind : "");
  }

  function showModal(title, text, btnText) {
    modalTitle.textContent = title;
    modalText.textContent = text;
    modalBtn.textContent = btnText;
    modal.classList.remove("hidden");
  }
  function hideModal() {
    modal.classList.add("hidden");
  }
  modalBtn.addEventListener("click", showHome);

  $("#backBtn").addEventListener("click", showHome);

  /* ---------- Timer ---------- */
  function formatTime(s) {
    const m = Math.floor(s / 60);
    const sec = s % 60;
    return String(m).padStart(2, "0") + ":" + String(sec).padStart(2, "0");
  }
  function startTimer() {
    stopTimer();
    state.seconds = 0;
    timerEl.textContent = formatTime(0);
    state.timerId = setInterval(() => {
      state.seconds++;
      timerEl.textContent = formatTime(state.seconds);
    }, 1000);
  }
  function stopTimer() {
    clearInterval(state.timerId);
    state.timerId = null;
  }

  /* ---------- Init ---------- */
  buildPad();
  renderHome();
})();
