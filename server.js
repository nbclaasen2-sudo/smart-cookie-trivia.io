// server.js
const http = require("node:http");
const next = require("next");
const { Server } = require("socket.io");


const dev = process.env.NODE_ENV !== "production";
const app = next({ dev });
const handle = app.getRequestHandler();
const CHOOSER_GRACE_MS = 4000;
const { getProvider, ALLOWED_CATEGORIES } = require("./lib/providers");


const PORT = parseInt(process.env.PORT || "3000", 10);
const triviaProvider = getProvider("mixed"); // or "opentdb" or "otqa"

const os = require("node:os");

function getLanIpv4() {
  const nets = os.networkInterfaces();
  const candidates = [];

  for (const name of Object.keys(nets)) {
    for (const net of nets[name] || []) {
      if (net.family !== "IPv4") continue;
      if (net.internal) continue;

      const ip = net.address;
      candidates.push(ip);
    }
  }

  // Prefer common private LAN ranges first
  const preferred = candidates.find((ip) => ip.startsWith("192.168.")) ||
                    candidates.find((ip) => ip.startsWith("10.")) ||
                    candidates.find((ip) => {
                      // 172.16.0.0 - 172.31.255.255
                      const m = ip.match(/^172\.(\d+)\./);
                      if (!m) return false;
                      const n = Number(m[1]);
                      return n >= 16 && n <= 31;
                    });

  return preferred || candidates[0] || null;
}

// Optional override (useful later for hosting / tunnels)
const PUBLIC_HOST = process.env.PUBLIC_HOST;      // e.g. "192.168.1.106" or a hostname
const PUBLIC_PORT = process.env.PUBLIC_PORT;      // e.g. "3000"
const PUBLIC_PROTOCOL = process.env.PUBLIC_PROTOCOL || "http";

function getBaseUrl() {
  const host = PUBLIC_HOST || getLanIpv4() || "localhost";
  const port = PUBLIC_PORT || String(PORT);
  return `${PUBLIC_PROTOCOL}://${host}:${port}`;
}

// -----------------------
// In-memory game store (MVP)
// -----------------------
/**
 * games[code] = {
 *   code, hostSocketId,
 *   settings: { turnsTotal, secondsPerQuestion, opentdb: { category, difficulty, type } },
 *   state: 'LOBBY'|'OFFER'|'QUESTION'|'RESULTS'|'FINISHED',
 *   players: Map<socketId, { id, name, ready, cookies }>,
 *   order: socketId[],
 *   chooserIndex: number,
 *   turnIndex: number,
 *   pool: InternalQuestion[],
 *   used: Set<string>,
 *   turn: { id, chooserId, offers, chosen, publicQuestion, correctChoiceIndex, endsAt, answers: Map<socketId, number|null> }
 * }
 */
const games = new Map();

function makeCode(len = 6) {
  const chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
  let out = "";
  for (let i = 0; i < len; i++) out += chars[Math.floor(Math.random() * chars.length)];
  return out;
}

function nowMs() {
  return Date.now();
}

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// -----------------------
// Typed-answer grading helpers
// -----------------------
function normalizeForCompare(s) {
  if (s === null || s === undefined) return "";
  // Lowercase, trim, remove punctuation, collapse whitespace
  return String(s)
    .toLowerCase()
    .trim()
    .replace(/[^a-z0-9\s]/g, " ")
    .replace(/\s+/g, " ")
    .trim();
}

// Levenshtein distance with an optional early-exit cap
function levenshtein(a, b, maxDist) {
  if (a === b) return 0;
  const alen = a.length;
  const blen = b.length;
  if (alen === 0) return blen;
  if (blen === 0) return alen;

  // Quick bound
  if (typeof maxDist === "number" && Math.abs(alen - blen) > maxDist) return maxDist + 1;

  // DP rows
  const prev = new Array(blen + 1);
  const curr = new Array(blen + 1);

  for (let j = 0; j <= blen; j++) prev[j] = j;

  for (let i = 1; i <= alen; i++) {
    curr[0] = i;
    let rowMin = curr[0];

    const ai = a.charCodeAt(i - 1);
    for (let j = 1; j <= blen; j++) {
      const cost = ai === b.charCodeAt(j - 1) ? 0 : 1;
      const del = prev[j] + 1;
      const ins = curr[j - 1] + 1;
      const sub = prev[j - 1] + cost;
      const v = Math.min(del, ins, sub);
      curr[j] = v;
      if (v < rowMin) rowMin = v;
    }

    if (typeof maxDist === "number" && rowMin > maxDist) return maxDist + 1;

    for (let j = 0; j <= blen; j++) prev[j] = curr[j];
  }

  return prev[blen];
}

function isTypedCorrect(userText, correctText) {
  const u = normalizeForCompare(userText);
  const c = normalizeForCompare(correctText);
  if (!u || !c) return false;

  const maxDist = u.length > 5 ? 2 : 1;
  const dist = levenshtein(u, c, maxDist);
  return dist <= maxDist;
}

function cookieFromDifficulty(difficulty) {
  if (difficulty === "easy") return 2;
  if (difficulty === "medium") return 3;
  return 5; // hard
}

function buildPublicQuestion(q) {
  // q: { id, category, cookieValue, prompt, correctAnswer, incorrectAnswers[], questionType? }
  const isTyped =
    q?.questionType === "typed" ||
    !Array.isArray(q?.incorrectAnswers) ||
    q.incorrectAnswers.length < 3;

  if (isTyped) {
    return {
      publicQ: {
        id: q.id,
        category: q.category,
        cookieValue: q.cookieValue,
        prompt: q.prompt,
        questionType: "typed",
        choices: [], // typed input; client should render an input instead of buttons
      },
      correctChoiceIndex: null,
    };
  }

  const choices = shuffle([q.correctAnswer, ...q.incorrectAnswers]);
  const correctChoiceIndex = choices.indexOf(q.correctAnswer);

  return {
    publicQ: {
      id: q.id,
      category: q.category,
      cookieValue: q.cookieValue,
      prompt: q.prompt,
      questionType: "multiple",
      choices,
    },
    correctChoiceIndex,
  };
}

function getPlayersArray(game) {
  return game.order
    .map((playerKey) => game.players.get(playerKey))
    .filter(Boolean)
    .map((p) => ({
      id: p.playerKey,          // IMPORTANT: id is now playerKey
      name: p.name,
      ready: p.ready,
      cookies: p.cookies,
      connected: !!p.socketId,
    }));
}


function broadcastLobby(io, game) {
  io.to(game.code).emit("lobby_update", {
    code: game.code,
    state: game.state,
    settings: game.settings,
    players: getPlayersArray(game),
    hostPlayerKey: game.hostPlayerKey,
    shareUrl: `${getBaseUrl()}/game/${game.code}`,
  });
}



async function ensurePool(game, minCount = 10) {
  if (game.pool.length >= minCount) return;

  // Keep difficulty if you want; type is always multiple choice in our provider usage.
  const difficulty = game.settings?.opentdb?.difficulty || "hard";

    // If a fill is already running, wait for it instead of starting another
    if (game.ensurePoolPromise) {
      await game.ensurePoolPromise;
      return;
    }
  // We’ll try a few category fetches per top-up so we can actually add questions,
  // without looping forever if a category returns empty.
    game.ensurePoolPromise = (async () => {
      // your existing logic here that calls provider.fetchBatch(...)
      // but keep maxRequestsThisTopup small (see Step 4)
      const maxRequestsThisTopup = 1;

      for (let attempt = 0; attempt < maxRequestsThisTopup && game.pool.length < minCount; attempt++) {
        let categoryId;

        if (triviaProvider.name === "otqa") {
          categoryId = game.fetchCursor;     // 0,1,2,3... rotates OTQA categories
          game.fetchCursor += 1;
        } else {
          categoryId = ALLOWED_CATEGORIES[game.fetchCursor % ALLOWED_CATEGORIES.length];
          game.fetchCursor += 1;
        }

        const batch = await triviaProvider.fetchBatch({
          amount: 20,
          categoryId,
          difficulty,
        });

        // Filter duplicates/used
        const fresh = batch.filter((q) => !game.used.has(q.id));
        game.pool.push(...fresh);
      }
    // If the provider returned nothing, we’ll just move on to the next category in the loop
  })();

  try {
    await game.ensurePoolPromise;
  } finally {
    game.ensurePoolPromise = null;
  }
}

async function warmupPoolForStart(io, game, {
  minCategories = 6,
  maxWaitMs = 25000,
} = {}) {
  const start = Date.now();
  let lastEmitAt = 0;

  // Helper: emit at most ~2 times per second (prevents spam)
  function emitStatus(final = false) {
    const now = Date.now();
    if (!final && now - lastEmitAt < 500) return;
    lastEmitAt = now;

    io.to(game.code).emit("warmup_status", {
      categoriesReady: countCategoriesInPool(game),
      minCategories,
      msRemaining: Math.max(0, maxWaitMs - (now - start)),
      final,
    });
  }

  emitStatus(false);

  while (countCategoriesInPool(game) < minCategories && (Date.now() - start) < maxWaitMs) {
    const target = Math.max(10, game.pool.length + 10);
    await ensurePool(game, target);

    emitStatus(false);
    await sleep(200);
  }

  // final emit so clients can hide the panel cleanly
  emitStatus(true);
}



function sleep(ms) {
  return new Promise((r) => setTimeout(r, ms));
}

function countCategoriesInPool(game) {
  const s = new Set();
  for (const q of game.pool) s.add(q.category);
  return s.size;
}

function startBackgroundPrefetch(io, game) {
  // Prevent duplicates
  if (game.prefetchInterval) return;

  // Track a single in-flight prefetch so interval ticks don't stack
  game.prefetchInFlight = false;

  const TARGET_POOL_SIZE = 60;     // keep plenty of upcoming offers ready
  const TARGET_CATEGORY_COUNT = 13; // gradually expand beyond the initial 4

  game.prefetchInterval = setInterval(async () => {
    try {
      // Only fetch while the game is actually running
      if (!["OFFER", "QUESTION", "RESULTS", "FINAL_WAGER", "FINAL_QUESTION", "FINAL_RESULTS"].includes(game.state)) return;

      // Don’t overlap fetches if one is still running
      if (game.prefetchInFlight) return;
      game.prefetchInFlight = true;

      const cats = countCategoriesInPool(game);

      // Decide whether to fetch:
      // 1) pool is getting low, OR
      // 2) category variety is still low (force a new batch even if pool is big)
      const needMorePool = game.pool.length < TARGET_POOL_SIZE;
      const needMoreCats = cats < TARGET_CATEGORY_COUNT;

      if (needMorePool) {
        await ensurePool(game, TARGET_POOL_SIZE);
      } else if (needMoreCats) {
        // Force one additional batch even if pool is already "full"
        // (ensurePool only triggers when pool.length < minCount)
        await ensurePool(game, game.pool.length + 10);
      }
    } catch (e) {
      // Soft-fail; don't crash the game if OpenTDB is slow/throttled
      // Optionally: console.log("[prefetch]", e.message);
    } finally {
      game.prefetchInFlight = false;
    }
  }, 6000); // every ~6s (safe with your provider’s 5.2s gate)
}

function stopBackgroundPrefetch(game) {
  if (game.prefetchInterval) {
    clearInterval(game.prefetchInterval);
    game.prefetchInterval = null;
  }
  game.prefetchInFlight = false;
}



// Picks up to n offers from game.pool with diversity constraints.
// Removes selected questions from game.pool (same behavior as your old pickOffers).
function pickOffersDiverse(game, n = 4) {
  const pool = game.pool;
  if (!pool || pool.length === 0) return [];

  // Track used (category|cookieValue) pairs so no duplicates of that pair can appear in offers
  const usedPair = new Set();

  // We’ll also strongly prefer unique categories.
  const picked = [];
  const pickedIndexes = new Set();
  const pickedCategories = new Set();

  // Helper: pick one question from pool matching constraints
  function tryPick({ requireNewCategory }) {
    // Create randomized index order
    const idxs = Array.from({ length: pool.length }, (_, i) => i);
    for (let i = idxs.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [idxs[i], idxs[j]] = [idxs[j], idxs[i]];
    }

    for (const idx of idxs) {
      if (pickedIndexes.has(idx)) continue;

      const q = pool[idx];
      const pairKey = `${q.category}||${q.cookieValue}`;

      if (usedPair.has(pairKey)) continue;

      if (requireNewCategory && pickedCategories.has(q.category)) continue;

      // Accept
      picked.push(q);
      pickedIndexes.add(idx);
      usedPair.add(pairKey);
      pickedCategories.add(q.category);
      return true;
    }
    return false;
  }

  // Pass 1: enforce unique categories
  while (picked.length < n) {
    const ok = tryPick({ requireNewCategory: true });
    if (!ok) break;
  }

  // Pass 2: allow category repeats if needed, still enforce unique (category,cookieValue)
  while (picked.length < n) {
    const ok = tryPick({ requireNewCategory: false });
    if (!ok) break;
  }

  // Remove picked from pool by index (descending so indices don’t shift)
  const toRemove = Array.from(pickedIndexes).sort((a, b) => b - a);
  for (const idx of toRemove) pool.splice(idx, 1);

  return picked;
}

function pickRandomFromArray(arr) {
  return arr[Math.floor(Math.random() * arr.length)];
}

function getPoolCategories(game) {
  const s = new Set();
  for (const q of game.pool) s.add(q.category);
  return Array.from(s);
}


function pickOffers(game, n = 4) {
  // random sample from pool
  const offers = [];
  const pool = game.pool;

  // if pool too small, caller should ensurePool beforehand
  for (let i = 0; i < n && pool.length > 0; i++) {
    const idx = Math.floor(Math.random() * pool.length);
    const [q] = pool.splice(idx, 1);
    offers.push(q);
  }
  return offers;
}

function startOfferPhase(io, game) {
  game.state = "OFFER";
  startBackgroundPrefetch(io, game);
  const chooserPlayerKey = game.order[game.chooserIndex];
  const chooser = game.players.get(chooserPlayerKey);
  const turnId = `t_${game.turnIndex + 1}_${Math.random().toString(16).slice(2)}`;
  

  if (!chooser || !chooser.socketId) {
    // chooser disconnected or missing; pick the next connected player
    const n = game.order.length;
    for (let i = 0; i < n; i++) {
      game.chooserIndex = (game.chooserIndex + 1) % n;
      const pk = game.order[game.chooserIndex];
      const p = game.players.get(pk);
      if (p && p.socketId) {
        return startOfferPhase(io, game); // re-run with a valid chooser
      }
    }

    // No one connected
    io.to(game.code).emit("error", { message: "No connected players to choose a question." });
    return;
  }
  const chooserSocketId = chooser.socketId;

  game.turn = {
    id: turnId,
    chooserId: chooserPlayerKey, // playerKey
    offers: [],
    chosen: null,
    publicQuestion: null,
    correctChoiceIndex: null,
    endsAt: null,
    answers: new Map(), // playerKey -> selectedIndex|null
  };

  // init answer map to null for all players (playerKey)
  for (const pk of game.players.keys()) game.turn.answers.set(pk, undefined);

  // pick offers (ensure pool first)
  Promise.resolve()
    .then(async () => {
      await ensurePool(game, 12);
      const offers = pickOffersDiverse(game, 4);
      game.turn.offers = offers;

      // chooser sees offer IDs
      io.to(chooserSocketId).emit("offer_questions", {
        code: game.code,
        turnId: game.turn.id,
        chooserId: chooserPlayerKey, // send stable id to clients
        offers: offers.map((q) => ({
          id: q.id,
          category: q.category,
          cookieValue: q.cookieValue,
        })),
      });

      // others just see “chooser is selecting”
      io.to(game.code).except(chooserSocketId).emit("offer_waiting", {
        code: game.code,
        turnId: game.turn.id,
        chooserId: chooserPlayerKey,
        offersPreview: offers.map((q) => ({
          category: q.category,
          cookieValue: q.cookieValue,
        })),
      });
    })
    .catch((e) => {
      io.to(game.code).emit("error", { message: `Failed to start offer phase: ${e.message}` });
    });
}

function emitAnswerStatus(io, game) {
  if (!game.turn || game.state !== "QUESTION") return;

  const connectedKeys = game.order.filter((k) => game.players.get(k)?.socketId);
  const pending = connectedKeys.filter((k) => game.turn.answers.get(k) === undefined);

  io.to(game.code).emit("answer_status", {
    code: game.code,
    turnId: game.turn.id,
    pendingPlayerKeys: pending,
  });
}


function emitFinalWagerStatus(io, game) {
  if (!game || game.state !== "FINAL_WAGER") return;

  const connectedKeys = game.order.filter((k) => game.players.get(k)?.socketId);
  const pending = connectedKeys.filter((k) => game.finalRound.wagers[k] === undefined);

  io.to(game.code).emit("final_wager_status", {
    code: game.code,
    pendingPlayerKeys: pending,
  });
}

function emitFinalAnswerStatus(io, game) {
  if (!game || game.state !== "FINAL_QUESTION") return;

  const connectedKeys = game.order.filter((k) => game.players.get(k)?.socketId);
  const pending = connectedKeys.filter((k) => game.finalRound.answers[k] === undefined);

  io.to(game.code).emit("final_answer_status", {
    code: game.code,
    pendingPlayerKeys: pending,
  });
}



function startQuestionPhase(io, game, chosenQuestion) {
  game.state = "QUESTION";
  // Store the internal question so typed answers can be graded server-side.
  game.turn.internalQuestion = chosenQuestion;
  const { publicQ, correctChoiceIndex } = buildPublicQuestion(chosenQuestion);

  game.turn.chosen = chosenQuestion.id;
  game.turn.publicQuestion = publicQ;
  game.turn.correctChoiceIndex = correctChoiceIndex;

  const endsAt = nowMs() + game.settings.secondsPerQuestion * 1000;
  game.turn.endsAt = endsAt;

  io.to(game.code).emit("question_revealed", {
    code: game.code,
    turnId: game.turn.id,
    chooserId: game.turn.chooserId,
    question: publicQ,
    endsAt,
    turnNumber: game.turnIndex + 1,
    turnsTotal: game.settings.turnsTotal,
  });
  emitAnswerStatus(io, game);

  // server-authoritative timer
  // Cancel any old question timer (safety)
  if (game.turnTimeout) {
    clearTimeout(game.turnTimeout);
    game.turnTimeout = null;
  }

  // Start a fresh timer for THIS question
  game.turnTimeout = setTimeout(() => {
    endQuestionPhase(io, game);
  }, game.settings.secondsPerQuestion * 1000 + 50);

}



function endQuestionPhase(io, game) {
  if (!game || game.state !== "QUESTION") return;

  // Cancel the active question timer (it may still be pending)
  if (game.turnTimeout) {
    clearTimeout(game.turnTimeout);
    game.turnTimeout = null;
  }


  game.state = "RESULTS";

  const q = game.turn.publicQuestion;
  const cookieValue = q.cookieValue;

  const playerResults = [];
  const qType = q.questionType || "multiple";

  if (qType === "typed") {
    const correctText = game.turn.internalQuestion?.correctAnswer ?? "";

    for (const [pk, submitted] of game.turn.answers.entries()) {
      const p = game.players.get(pk);
      if (!p) continue;

      if (submitted === null || submitted === undefined || String(submitted).trim() === "") {
        playerResults.push({ playerId: pk, outcome: "blank", delta: 0, textAnswer: null });
        continue;
      }

      const ok = isTypedCorrect(submitted, correctText);

      if (ok) {
        p.cookies += cookieValue;
        playerResults.push({ playerId: pk, outcome: "correct", delta: cookieValue, textAnswer: String(submitted) });
      } else {
        p.cookies -= cookieValue;
        playerResults.push({ playerId: pk, outcome: "incorrect", delta: -cookieValue, textAnswer: String(submitted) });
      }
    }

    // store and broadcast results + leaderboard
    const resultsPayload = {
      code: game.code,
      turnId: game.turn.id,
      questionType: "typed",
      correctChoiceIndex: null,
      correctAnswerText: correctText,
      playerResults,
      leaderboard: getPlayersArray(game).sort((a, b) => b.cookies - a.cookies),
    };

    game.lastResults = resultsPayload;

    // ✅ push updated cookies + state to everyone
    broadcastLobby(io, game);

    io.to(game.code).emit("results", resultsPayload);

    // mark used
    game.used.add(game.turn.publicQuestion.id);

    // next turn or finish
    // Cancel any previous results delay timer (safety)
    if (game.resultsTimeout) {
      clearTimeout(game.resultsTimeout);
      game.resultsTimeout = null;
    }

    game.resultsTimeout = setTimeout(() => {
      game.resultsTimeout = null;

      game.turnIndex += 1;

      if (game.turnIndex >= game.settings.turnsTotal) {
        startFinalWagerPhase(io, game).catch((e) => {
          io.to(game.code).emit("error", { message: `Final round failed: ${e.message}` });
          finishGame(io, game);
        });
        return;
      }

      game.chooserIndex = (game.chooserIndex + 1) % game.order.length;
      startOfferPhase(io, game);
    }, 8000);

    return;
  }

  // Multiple-choice grading
  const correctIdx = game.turn.correctChoiceIndex;

  for (const [pk, selectedIndex] of game.turn.answers.entries()) {
    const p = game.players.get(pk);
    if (!p) continue;

    if (selectedIndex === null || selectedIndex === undefined) {
      playerResults.push({ playerId: pk, outcome: "blank", delta: 0, selectedIndex: null });
    } else if (selectedIndex === correctIdx) {
      p.cookies += cookieValue;
      playerResults.push({ playerId: pk, outcome: "correct", delta: cookieValue, selectedIndex });
    } else {
      p.cookies -= cookieValue;
      playerResults.push({ playerId: pk, outcome: "incorrect", delta: -cookieValue, selectedIndex });
    }
  }
  // mark used
  game.used.add(game.turn.publicQuestion.id);

  // store and broadcast results + leaderboard
  const resultsPayload = {
    code: game.code,
    turnId: game.turn.id,
    correctChoiceIndex: correctIdx,
    correctAnswerText: q.choices[correctIdx],
    playerResults,
    leaderboard: getPlayersArray(game).sort((a, b) => b.cookies - a.cookies),
  };

  game.lastResults = resultsPayload;

  // ✅ push updated cookies + state to everyone
  broadcastLobby(io, game);

  io.to(game.code).emit("results", resultsPayload);


  // next turn or finish
  // Cancel any previous results delay timer (safety)
  if (game.resultsTimeout) {
    clearTimeout(game.resultsTimeout);
    game.resultsTimeout = null;
  }

  game.resultsTimeout = setTimeout(() => {
    game.resultsTimeout = null;

    // advance chooser/turn and startOfferPhase(...)
    game.turnIndex += 1;

    if (game.turnIndex >= game.settings.turnsTotal) {
      startFinalWagerPhase(io, game).catch((e) => {
        io.to(game.code).emit("error", { message: `Final round failed: ${e.message}` });
        // As a fallback, at least finish the game cleanly
        finishGame(io, game);
      });
      return;
    }


    // advance chooser
    game.chooserIndex = (game.chooserIndex + 1) % game.order.length;
    startOfferPhase(io, game);
  }, 8000); // 8 second delay to display leaderboard
}

async function startFinalWagerPhase(io, game) {
  game.state = "FINAL_WAGER";

  // Make sure we have enough pool to pick a category
  await ensurePool(game, Math.max(20, game.pool.length + 10));

  const cats = getPoolCategories(game);
  console.log("[final] pool size:", game.pool.length, "cats:", countCategoriesInPool(game));

  if (cats.length === 0) {
    // fallback: start game finished if no questions exist at all
    finishGame(io, game);
    return;
  }

  const category = pickRandomFromArray(cats);

  game.finalRound.category = category;
  game.finalRound.question = null;
  game.finalRound.wagers = {};
  game.finalRound.answers = {};
  // Keep final wager timer consistent with the countdown clients display (endsAt)
  const wagerMs = (game.settings.secondsPerQuestion || 20) * 1000;
  game.finalRound.wagerEndsAt = nowMs() + wagerMs;

  // Broadcast so clients show wager UI
  io.to(game.code).emit("final_wager_start", {
    code: game.code,
    category,
    players: getPlayersArray(game).map(p => ({
      playerKey: p.id,
      name: p.name,
      cookies: p.cookies,
    })),
    endsAt: game.finalRound.wagerEndsAt,
  });
  emitFinalWagerStatus(io, game);

  // If everyone submits wagers early, you’ll end early (see handler below)
  clearTimeout(game.finalWagerTimeout);
  game.finalWagerTimeout = setTimeout(() => {
    endFinalWagerPhase(io, game);
  }, Math.max(0, game.finalRound.wagerEndsAt - nowMs()) + 50);
}

async function endFinalWagerPhase(io, game) {
  if (game.state !== "FINAL_WAGER") return;

  clearTimeout(game.finalWagerTimeout);
  game.finalWagerTimeout = null;

  const category = game.finalRound.category;

  // Ensure we have at least one question in the chosen category
  for (let tries = 0; tries < 4; tries++) {
    const idx = game.pool.findIndex(q => q.category === category);
    if (idx !== -1) {
      const q = game.pool.splice(idx, 1)[0];
      game.finalRound.question = q;
      break;
    }
    // fetch a bit more and try again
    await ensurePool(game, game.pool.length + 10);
  }

  if (!game.finalRound.question) {
    // fallback: if still none, pick any question
    await ensurePool(game, Math.max(20, game.pool.length + 10));
    if (game.pool.length === 0) {
      finishGame(io, game);
      return;
    }
    game.finalRound.question = game.pool.shift();
    game.finalRound.category = game.finalRound.question.category;
  }

  startFinalQuestionPhase(io, game);
}

function startFinalQuestionPhase(io, game) {
  game.state = "FINAL_QUESTION";

  const q = game.finalRound.question;
  const { publicQ, correctChoiceIndex } = buildPublicQuestion(q);
  game.finalRound.publicQuestion = publicQ;
  game.finalRound.correctChoiceIndex = correctChoiceIndex;

  // reset per-player answers
  game.finalRound.answers = {};

  game.finalRound.questionEndsAt = nowMs() + game.settings.secondsPerQuestion * 1000;
  

  io.to(game.code).emit("final_question_start", {
    code: game.code,
    category: game.finalRound.category,
    question: publicQ, // <- send the actual public question object
    endsAt: game.finalRound.questionEndsAt,
  });
  emitFinalAnswerStatus(io, game);

  clearTimeout(game.finalQuestionTimeout);
  game.finalQuestionTimeout = setTimeout(() => {
    endFinalQuestionPhase(io, game);
  }, game.settings.secondsPerQuestion * 1000 + 50);
}

function endFinalQuestionPhase(io, game) {
  if (game.state !== "FINAL_QUESTION") return;

  clearTimeout(game.finalQuestionTimeout);
  game.finalQuestionTimeout = null;

  game.state = "FINAL_RESULTS";

  const q = game.finalRound.question;
  const qType = game.finalRound.publicQuestion?.questionType || "multiple";
  const correctIdx = game.finalRound.correctChoiceIndex;
  const correctText = q?.correctAnswer ?? "";

  // Grade each player
  for (const pk of game.order) {
    const p = game.players.get(pk);
    if (!p) continue;

    const wager = Number(game.finalRound.wagers[pk] ?? 0) || 0;
    const ans = game.finalRound.answers[pk];

    let isCorrect = false;

    if (qType === "typed") {
      if (ans !== null && ans !== undefined && String(ans).trim() !== "") {
        isCorrect = isTypedCorrect(ans, correctText);
      } else {
        isCorrect = false;
      }
    } else {
      isCorrect = ans === correctIdx;
    }

    if (wager > 0) {
      if (isCorrect) p.cookies += wager;
      else p.cookies -= wager;
    }
  }

  // ✅ push updated cookies to everyone
  broadcastLobby(io, game);

  const players = getPlayersArray(game);
  // Send results + updated leaderboard
  io.to(game.code).emit("final_results", {
    code: game.code,
    correctChoiceIndex: (game.finalRound.publicQuestion?.questionType === "typed") ? null : correctIdx,
    correctAnswerText: (game.finalRound.publicQuestion?.questionType === "typed") ? correctText : game.finalRound.publicQuestion.choices[correctIdx], // ✅ add
    leaderboard: players.slice().sort((a, b) => b.cookies - a.cookies),
  });

  clearTimeout(game.finalResultsTimeout);
  game.finalResultsTimeout = setTimeout(() => {
    finishGame(io, game);
  }, 4000); // your existing “show leaderboard for 4s”
}




function finishGame(io, game) {
  game.state = "FINISHED";

  // stop background prefetch if you added it earlier
  stopBackgroundPrefetch?.(game);

  const leaderboard = getPlayersArray(game).slice().sort((a, b) => b.cookies - a.cookies);

  io.to(game.code).emit("game_finished", {
    code: game.code,
    leaderboard,
  });

  broadcastLobby(io, game);
}


function sendStateSync(io, game, pk) {
  const p = game.players.get(pk);
  if (!p?.socketId) return;

  // If no active turn, nothing else to sync.
  if (!game.turn) return;

  if (game.state === "OFFER") {
    const chooserPk = game.turn.chooserId;
    if (pk === chooserPk) {
      io.to(p.socketId).emit("offer_questions", {
        code: game.code,
        turnId: game.turn.id,
        chooserId: chooserPk,
        offers: game.turn.offers.map((q) => ({
          id: q.id,
          category: q.category,
          cookieValue: q.cookieValue,
        })),
      });
    } else {
      io.to(p.socketId).emit("offer_waiting", {
        code: game.code,
        turnId: game.turn.id,
        chooserId: chooserPk,
        offersPreview: game.turn.offers.map((q) => ({
          category: q.category,
          cookieValue: q.cookieValue,
        })),
      });
    }
  }

  if (game.state === "QUESTION" && game.turn.publicQuestion) {
    io.to(p.socketId).emit("question_revealed", {
      code: game.code,
      turnId: game.turn.id,
      question: game.turn.publicQuestion,
      endsAt: game.turn.endsAt,

      // ✅ restore this player's saved choice
      myAnswer: (typeof game.turn.answers.get(pk) === "number" || game.turn.answers.get(pk) === null || game.turn.answers.get(pk) === undefined) ? game.turn.answers.get(pk) : undefined, // number | null | undefined
      myAnswerText: (typeof game.turn.answers.get(pk) === "string") ? game.turn.answers.get(pk) : undefined, // string | null | undefined
    });
  }

  if (game.state === "FINISHED" && game.lastResults) {
    io.to(p.socketId).emit("game_finished", {
      code: game.code,
      leaderboard: game.lastResults.leaderboard,
    });
  }

  if (game.state === "FINAL_WAGER") {
    io.to(p.socketId).emit("lobby_update", {
      code: game.code,
      state: game.state,
      settings: game.settings,
      players: getPlayersArray(game),
      hostPlayerKey: game.hostPlayerKey,
      shareUrl: game.shareUrl, // if you store it, otherwise omit
    });

    io.to(p.socketId).emit("final_wager_start", {
      code: game.code,
      category: game.finalRound.category,
      players: getPlayersArray(game).map((p) => ({
        playerKey: p.id,
        name: p.name,
        cookies: p.cookies,
      })),
      endsAt: game.finalRound.wagerEndsAt || (nowMs() + 30000), // safe fallback
    });

    // Optional: if this socket already submitted a wager, acknowledge it
    
    if (pk && game.finalRound.wagers && game.finalRound.wagers[pk] !== undefined) {
      io.to(p.socketId).emit("final_wager_ack", { wager: game.finalRound.wagers[pk] });
    }
  }

  if (game.state === "FINAL_QUESTION") {
    io.to(p.socketId).emit("lobby_update", {
      code: game.code,
      state: game.state,
      settings: game.settings,
      players: getPlayersArray(game),
      hostPlayerKey: game.hostPlayerKey,
      shareUrl: game.shareUrl,
    });

    const q = game.finalRound.question;
    if (q) {
      // IMPORTANT: use the same public question that was created when the final question started.
      // If you didn't store it, rebuild it (it will reshuffle unless you store it).
      // Best: store game.finalRound.publicQuestion when starting final question.
      const publicQ = game.finalRound.publicQuestion || buildPublicQuestion(q).publicQ;

      io.to(p.socketId).emit("final_question_start", {
        code: game.code,
        category: game.finalRound.category,
        question: publicQ,
        endsAt: game.finalRound.questionEndsAt || (nowMs() + 5000),

        // ✅ restore this player's saved choice
        myAnswer: (typeof game.finalRound.answers?.[pk] === "number" || game.finalRound.answers?.[pk] === null || game.finalRound.answers?.[pk] === undefined) ? game.finalRound.answers?.[pk] : undefined, // number | null | undefined
        myAnswerText: (typeof game.finalRound.answers?.[pk] === "string") ? game.finalRound.answers?.[pk] : undefined, // string | null | undefined
      });
    }
  }


  if (game.state === "RESULTS" && game.lastResults) {
    io.to(p.socketId).emit("results", game.lastResults);
  }
}


app.prepare().then(() => {
  const httpServer = http.createServer((req, res) => handle(req, res));

  const io = new Server(httpServer, {
    cors: { origin: "*" },
    pingInterval: 25000,
    pingTimeout: 60000,
  });

  io.on("connection", (socket) => {
    // ---- Create game (host) ----
    socket.on("create_game", async ({ playerKey, name, turnsTotal, secondsPerQuestion, opentdb }) => {
      try {
        let code = makeCode();
        while (games.has(code)) code = makeCode();

        const game = {
          code,
          ensurePoolPromise: null,
          prefetchInterval: null,
          prefetchInFlight: false,
          pendingChooserTimeout: null,
          pendingChooserTurnId: null,
          pendingChooserPlayerKey: null,
          turnTimeout: null,     // timer for QUESTION phase (per question)
          resultsTimeout: null,  // timer for RESULTS delay before next offer
          hostPlayerKey: null,            // stable identity
          hostSocketId: socket.id,        // superfluous but does not break anything
          settings: {
            turnsTotal: Math.max(1, Math.min(50, Number(turnsTotal) || 10)),
            secondsPerQuestion: Math.max(5, Math.min(120, Number(secondsPerQuestion) || 30)),
            opentdb: {
              category: Number(opentdb?.category) || 17,
              difficulty: opentdb?.difficulty || "hard",
              type: opentdb?.type || "multiple",
            },
          },
          state: "LOBBY",
          players: new Map(),
          order: [],
          socketToPlayerKey: new Map(),   // Map<socket.id, playerKey>
          chooserIndex: 0,
          turnIndex: 0,
          pool: [],
          used: new Set(),
          turn: null,
          fetchCursor: 0, // rotates through ALLOWED_CATEGORIES
          finalRound: {
            category: null,      // string: chosen final category
            question: null,      // InternalQuestion object (same format you use in pool)
            wagers: {},          // map: playerKey -> number
            answers: {},         // map: playerKey -> choiceIndex (number) OR null for "no guess"
            correctChoiceIndex: null, // number: index of correct choice after shuffling (server-truth)
          },

          finalWagerTimeout: null,
          finalQuestionTimeout: null,
          finalResultsTimeout: null,
        };

        games.set(code, game);

        // host auto-joins as player
        socket.join(code);

        const hostKey = playerKey || `pk_${Math.random().toString(16).slice(2)}${Date.now()}`;

        game.players.set(hostKey, {
          playerKey: hostKey,
          socketId: socket.id,
          name: name || "Host",
          ready: false,
          cookies: 0,
        });

        game.order.push(hostKey);
        game.socketToPlayerKey.set(socket.id, hostKey);

        game.hostPlayerKey = hostKey;


        // prefetch one batch for snappy start
        await ensurePool(game, 20);

        broadcastLobby(io, game);

        socket.emit("game_created", { code });
      } catch (e) {
        socket.emit("error", { message: e.message });
      }
    });

    // ---- Join game ----
    socket.on("join_game", ({ code, playerKey, name }) => {
      const game = games.get(code);
      if (!game) {
        socket.emit("error", { message: "Game not found." });
        return;
      }
      

      socket.join(code);

      const pk = playerKey || `pk_${Math.random().toString(16).slice(2)}${Date.now()}`;
      const existing = game.players.get(pk);

      if (existing) {
        // Reconnect: keep ready/cookies, just update socketId + name
        existing.socketId = socket.id;
        // If the chooser reconnects during OFFER within the grace window, cancel reassignment
        if (
          game.state === "OFFER" &&
          game.turn &&
          game.turn.chooserId === pk &&
          game.pendingChooserTimeout &&
          game.pendingChooserTurnId === game.turn.id &&
          game.pendingChooserPlayerKey === pk
        ) {
          clearTimeout(game.pendingChooserTimeout);
          game.pendingChooserTimeout = null;
          game.pendingChooserTurnId = null;
          game.pendingChooserPlayerKey = null;
        }

        if (name) existing.name = name;
      } else {
        // New player
        game.players.set(pk, {
          playerKey: pk,
          socketId: socket.id,
          name: name || "Player",
          ready: false,
          cookies: 0,
        });
        game.order.push(pk);

        // if a turn is active, they should be included in answer tracking
        if (game.turn && game.turn.answers && !game.turn.answers.has(pk)) {
          game.turn.answers.set(pk, undefined);
        }
      }

      game.socketToPlayerKey.set(socket.id, pk);

      // Ensure host exists (if host disconnected earlier, for example)
      if (!game.hostPlayerKey) game.hostPlayerKey = game.order[0];

      broadcastLobby(io, game);
       
      // ✅ send a “catch-up” snapshot to THIS socket only
      sendStateSync(io, game, pk);

      socket.emit("joined", { code });

    });

    // ---- Ready toggle ----
    socket.on("toggle_ready", ({ code, playerKey, ready }) => {
      const game = games.get(code);
      if (!game) return;

      const pk = playerKey || game.socketToPlayerKey.get(socket.id);
      if (!pk) return;

      const p = game.players.get(pk);
      if (!p) return;

      p.ready = !!ready;

      // keep socket mapping fresh
      p.socketId = socket.id;
      game.socketToPlayerKey.set(socket.id, pk);

      broadcastLobby(io, game);

      // ✅ Auto-start when all players (>=2) are ready
      if (game.state === "LOBBY") {
        const players = getPlayersArray(game).filter((x) => x.connected);
        const allReady = players.length >= 1 && players.every((x) => x.ready);

        if (allReady) {
          game.turnIndex = 0;
          game.chooserIndex = 0;
          warmupPoolForStart(io, game, { minCategories: 4, maxWaitMs: 25000 })
            .then(() => startOfferPhase(io, game))
            .catch((e) => io.to(game.code).emit("error", { message: e.message }));

        }
      }
    });

    // ---- Start game (host) ----
    socket.on("start_game", async ({ code }) => {
      const game = games.get(code);
      if (!game) return;

      const callerPk = game.socketToPlayerKey.get(socket.id);
      if (!callerPk || callerPk !== game.hostPlayerKey) {
        socket.emit("error", { message: "Only the host can start." });
        return;
      }

      if (game.state !== "LOBBY") return;

      const players = getPlayersArray(game).filter((p) => p.connected);
      if (players.length < 1) {
        socket.emit("error", { message: "Need at least 1 player." });
        return;
      }
      if (players.some((p) => !p.ready)) {
        socket.emit("error", { message: "Not everyone is ready." });
        return;
      }

      game.turnIndex = 0;
      game.chooserIndex = 0;
      await warmupPoolForStart(io, game, { minCategories: 4, maxWaitMs: 25000 });
      startOfferPhase(io, game);

    });

    
    // ---- Restart game (host) ----
    socket.on("restart_game", ({ code }) => {
      const game = games.get(code);
      if (!game) return socket.emit("error", { message: "Game not found." });

      // Only host can restart
      const callerPk = game.socketToPlayerKey?.get(socket.id);
      if (!callerPk || callerPk !== game.hostPlayerKey) {
        return socket.emit("error", { message: "Only the host can start a new game." });
      }

      // Clear any pending timers (if you implemented chooser grace)
      if (game.pendingChooserTimeout) {
        clearTimeout(game.pendingChooserTimeout);
        game.pendingChooserTimeout = null;
        game.pendingChooserTurnId = null;
        game.pendingChooserPlayerKey = null;
      }
      if (game.turnTimeout) {
        clearTimeout(game.turnTimeout);
        game.turnTimeout = null;
      }
      if (game.resultsTimeout) {
        clearTimeout(game.resultsTimeout);
        game.resultsTimeout = null;
      }
      clearTimeout(game.finalWagerTimeout);
      clearTimeout(game.finalQuestionTimeout);
      clearTimeout(game.finalResultsTimeout);

      game.finalWagerTimeout = null;
      game.finalQuestionTimeout = null;
      game.finalResultsTimeout = null;

      // also reset final round data
      game.finalRound = {
        category: null,
        question: null,
        wagers: {},
        answers: {},
        correctChoiceIndex: null,
      };

      stopBackgroundPrefetch(game);

      // Reset game state but KEEP: code + settings + players
      
      
      game.state = "LOBBY";
      game.turnIndex = 0;
      game.chooserIndex = 0;
      game.turn = null;

      // Reset question tracking
      game.pool = [];
      game.used = new Set();

      // Clear last results snapshot if you store it
      game.lastResults = null;

      // Reset player scores + readiness
      for (const p of game.players.values()) {
        p.cookies = 0;
        p.ready = false;
      }

      // Push lobby state to everyone
      broadcastLobby(io, game);

      // Optional: tell clients to clear local UI immediately
      io.to(game.code).emit("game_restarted", { code: game.code });
    });


    // ---- Chooser picks question ----
    socket.on("choose_question", ({ code, turnId, questionId }) => {
      const game = games.get(code);
      if (!game || game.state !== "OFFER") return;
      if (!game.turn || game.turn.id !== turnId) return;
      const pk = game.socketToPlayerKey.get(socket.id);
      if (!pk || pk !== game.turn.chooserId) return;

      const chosen = game.turn.offers.find((q) => q.id === questionId);
      if (!chosen) return;

      startQuestionPhase(io, game, chosen);
    });

    // ---- Player submits choice (multiple-choice index OR typed text) ----
    socket.on("submit_choice", ({ code, turnId, playerKey, selectedIndex, textAnswer }) => {
      const game = games.get(code);
      if (!game || game.state !== "QUESTION") return;
      if (!game.turn || game.turn.id !== turnId) return;

      const endsAt = game.turn.endsAt;
      if (!endsAt || nowMs() > endsAt) return;

      // Never trust a random playerKey from the client
      const pk = game.socketToPlayerKey.get(socket.id) || playerKey;
      if (!pk) return;

      const p = game.players.get(pk);
      if (!p) return;

      const qType = game.turn.publicQuestion?.questionType || "multiple";

      if (qType === "typed") {
        // Treat empty/whitespace as "no guess"
        let ans = (textAnswer === null || textAnswer === undefined) ? null : String(textAnswer);
        if (ans !== null) {
          ans = ans.trim();
          if (!ans) ans = null;
        }
        game.turn.answers.set(pk, ans);
      } else {
        const idx = selectedIndex === null ? null : Number(selectedIndex);
        if (idx !== null && (idx < 0 || idx > 3)) return;
        game.turn.answers.set(pk, idx);
      }

      socket.emit("answer_ack", { turnId });

      // ✅ update answer status for everyone
      emitAnswerStatus(io, game);

      // Auto-end early if all CONNECTED players have submitted
      const connectedKeys = game.order.filter((k) => game.players.get(k)?.socketId);
      const allSubmitted =
        connectedKeys.length > 0 &&
        connectedKeys.every((k) => game.turn.answers.get(k) !== undefined);

      if (allSubmitted) endQuestionPhase(io, game);
    });
    
    // ---- Player sets final wager ----
    socket.on("final_set_wager", ({ code, wager }) => {
      const game = games.get(code);
      if (!game) return;
      if (game.state !== "FINAL_WAGER") return;

      const pk = game.socketToPlayerKey.get(socket.id);
      if (!pk) return;

      const p = game.players.get(pk);
      if (!p) return;

      const max = Math.max(0, Number(p.cookies) || 0);
      let w = Number(wager);
      if (!Number.isFinite(w)) w = 0;
      w = Math.max(0, Math.min(max, Math.floor(w)));

      game.finalRound.wagers[pk] = w;

      socket.emit("final_wager_ack", { wager: w });

      // ✅ update final wager status for everyone
      emitFinalWagerStatus(io, game);

      // Auto-end early if all CONNECTED players have wagered
      const connectedKeys = game.order.filter((k) => game.players.get(k)?.socketId);
      const allWagered =
        connectedKeys.length > 0 &&
        connectedKeys.every((k) => game.finalRound.wagers[k] !== undefined);

      if (allWagered) endFinalWagerPhase(io, game);
    });

    // ---- Player submits final question choice (multiple-choice index OR typed text) ----
    socket.on("final_submit_choice", ({ code, choiceIndex, textAnswer }) => {
      const game = games.get(code);
      if (!game) return;
      if (game.state !== "FINAL_QUESTION") return;

      const pk = game.socketToPlayerKey.get(socket.id);
      if (!pk) return;

      const p = game.players.get(pk);
      if (!p) return;

      const qType = game.finalRound.publicQuestion?.questionType || "multiple";

      if (qType === "typed") {
        let ans = (textAnswer === null || textAnswer === undefined) ? null : String(textAnswer);
        if (ans !== null) {
          ans = ans.trim();
          if (!ans) ans = null;
        }
        game.finalRound.answers[pk] = ans;
      } else {
        // choices are stored in game.finalRound.publicQuestion.choices (public question)
        const n = game.finalRound.publicQuestion?.choices?.length ?? 4;

        const c = (choiceIndex === null || choiceIndex === undefined) ? null : Number(choiceIndex);
        if (c !== null && (!Number.isInteger(c) || c < 0 || c >= n)) return;

        game.finalRound.answers[pk] = c;
      }

      socket.emit("answer_ack", { ok: true, final: true });

      // ✅ update final answer status for everyone
      emitFinalAnswerStatus(io, game);

      const connectedKeys = game.order.filter((k) => game.players.get(k)?.socketId);
      const allAnswered =
        connectedKeys.length > 0 &&
        connectedKeys.every((k) => game.finalRound.answers[k] !== undefined);

      if (allAnswered) endFinalQuestionPhase(io, game);
    });



    // ---- Disconnect cleanup ----
    socket.on("disconnect", () => {
      for (const [code, game] of games.entries()) {
      const pk = game.socketToPlayerKey?.get(socket.id);
      if (!pk) continue;

      const p = game.players.get(pk);
      if (p) {
        // ✅ mark offline, keep them in the game
        p.socketId = null;
      }

      // remove socket->player mapping
      game.socketToPlayerKey.delete(socket.id);

      // If chooser disconnected during OFFER, advance to next connected chooser
      if (game.turn && game.turn.chooserId === pk && game.state === "OFFER") {
        // If there's already a pending timer for this exact turn+chooser, do nothing.
        if (
          game.pendingChooserTimeout &&
          game.pendingChooserTurnId === game.turn.id &&
          game.pendingChooserPlayerKey === pk
        ) {
          // already scheduled
        } else {
          // clear any stale timer
          if (game.pendingChooserTimeout) {
            clearTimeout(game.pendingChooserTimeout);
            game.pendingChooserTimeout = null;
          }

          game.pendingChooserTurnId = game.turn.id;
          game.pendingChooserPlayerKey = pk;

          game.pendingChooserTimeout = setTimeout(() => {
            // Re-check conditions after grace period
            if (!games.has(game.code)) return;
            const g = games.get(game.code);
            if (!g || g.state !== "OFFER" || !g.turn) return;

            // still the same turn and same chooser?
            if (g.turn.id !== game.pendingChooserTurnId) return;
            if (g.turn.chooserId !== game.pendingChooserPlayerKey) return;

            // If chooser reconnected, cancel.
            const chooserNow = g.players.get(g.turn.chooserId);
            if (chooserNow && chooserNow.socketId) {
              g.pendingChooserTimeout = null;
              g.pendingChooserTurnId = null;
              g.pendingChooserPlayerKey = null;
              return;
            }

            // Find next connected player to be chooser
            const n = g.order.length;
            if (!n) return;

            let foundIndex = null;
            for (let step = 1; step <= n; step++) {
              const idx = (g.chooserIndex + step) % n;
              const pk2 = g.order[idx];
              const p2 = g.players.get(pk2);
              if (p2 && p2.socketId) {
                foundIndex = idx;
                break;
              }
            }

            // If nobody is connected, don't advance (avoids "no connected players" spam)
            if (foundIndex === null) {
              g.pendingChooserTimeout = null;
              g.pendingChooserTurnId = null;
              g.pendingChooserPlayerKey = null;
              broadcastLobby(io, g);
              return;
            }

            // Advance chooser and restart offer phase
            g.chooserIndex = foundIndex;

            g.pendingChooserTimeout = null;
            g.pendingChooserTurnId = null;
            g.pendingChooserPlayerKey = null;
   
            startOfferPhase(io, g);
          }, CHOOSER_GRACE_MS);
        }
      }


      broadcastLobby(io, game);

        // if no players remain, delete after a short grace period (helps during navigation/reconnect)
        if (game.players.size === 0) {
          const deleteCode = code;
          setTimeout(() => {
            const g = games.get(deleteCode);
            if (g && g.players.size === 0 && g.state === "LOBBY") {
              games.delete(deleteCode);
            }
          }, 15000); // 15 seconds
        }
      }
    });
  });

  httpServer.listen(PORT, () => {
    console.log(`> Ready on http://localhost:${PORT}`);
  });
});
 
