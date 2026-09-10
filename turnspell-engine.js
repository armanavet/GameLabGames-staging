/* ============================================================================
   turnspell-engine.js — cube state, moves, and puzzle generation. No DOM.

   Turnspell is Wordle crossed with a Rubik's cube: every sticker carries a
   letter, and the player turns faces until the front face spells the goal
   word in reading order.

   THE CENTRAL DESIGN DECISION IS DIFFICULTY. A genuinely scrambled letter
   cube is a speedcuber's puzzle — the reference prototype needed 38 moves for
   a four-letter word, which is nobody's coffee break. So puzzles are built
   BACKWARDS: place the word, fill the rest, then scramble by a known handful
   of turns. Every puzzle is therefore solvable in at most that many moves by
   construction, and the ladder of goal words is what supplies the challenge
   rather than raw scramble depth.

   Like the sudoku, the date IS the puzzle — a seeded PRNG means every reader
   opening 2026-09-10 gets identical letters with no request to a backend, and
   there is nothing to author, schedule or withhold.

   ---------------------------------------------------------------------------
   Geometry. A sticker is { p:[x,y,z], n:[x,y,z], ch } where p is its cubie
   (each component -1/0/1) and n its outward normal. Modelling stickers in
   real coordinates rather than as six arrays of nine means a face turn is
   just a 90-degree integer rotation of p and n — no hand-written permutation
   tables to get subtly wrong — and the same vectors drive the CSS 3D
   placement in the player, so the logic and the picture cannot disagree.
   ========================================================================= */
(function (root) {
  'use strict';

  /* ---------- deterministic randomness (same approach as the sudoku) ------ */
  function hashSeed(str) {
    let h = 2166136261 >>> 0;
    for (let i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = Math.imul(h, 16777619) >>> 0; }
    return h >>> 0;
  }
  function mulberry32(a) {
    return function () {
      a = (a + 0x6D2B79F5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), 1 | t);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  const pick = (arr, rng) => arr[Math.floor(rng() * arr.length)];

  /* ---------- the six faces ----------
     `up` and `right` are the face's own screen basis, which fixes reading
     order; `cw` rotates a vector a quarter turn clockwise as seen from
     outside that face. Both were derived from the same right-handed world
     (Y up, Z toward the viewer) so the player can reuse them verbatim. */
  const FACES = {
    U: { n: [0, 1, 0],  up: [0, 0, -1], right: [1, 0, 0],  cw: v => [-v[2], v[1], v[0]] },
    D: { n: [0, -1, 0], up: [0, 0, 1],  right: [1, 0, 0],  cw: v => [v[2], v[1], -v[0]] },
    R: { n: [1, 0, 0],  up: [0, 1, 0],  right: [0, 0, -1], cw: v => [v[0], v[2], -v[1]] },
    L: { n: [-1, 0, 0], up: [0, 1, 0],  right: [0, 0, 1],  cw: v => [v[0], -v[2], v[1]] },
    F: { n: [0, 0, 1],  up: [0, 1, 0],  right: [1, 0, 0],  cw: v => [v[1], -v[0], v[2]] },
    B: { n: [0, 0, -1], up: [0, 1, 0],  right: [-1, 0, 0], cw: v => [-v[1], v[0], v[2]] },
  };
  const FACE_IDS = ['U', 'D', L_ID(), 'R', 'F', 'B'];
  function L_ID() { return 'L'; }               // keeps the list readable above
  const MOVES = [];
  FACE_IDS.forEach(f => { MOVES.push(f); MOVES.push(f + "'"); });

  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const axisOf = f => FACES[f].n.findIndex(c => c !== 0);
  const signOf = f => FACES[f].n[axisOf(f)];

  /* Reading order within a face: row-major as a person sees it, so slot 0 is
     top-left and a word wraps the way text does. */
  const slotOf = (f, p) => (1 - dot(p, FACES[f].up)) * 3 + (dot(p, FACES[f].right) + 1);

  /* ---------- state ----------
     A flat array of 54 stickers. Sticker identity is its index and never
     changes, which is what lets the player keep one DOM node per sticker and
     merely re-place it after every turn. */
  function solvedShell(letters) {
    const out = [];
    FACE_IDS.forEach(f => {
      const F = FACES[f], a = axisOf(f), s = signOf(f);
      for (let i = -1; i <= 1; i++) for (let j = -1; j <= 1; j++) {
        const p = [0, 0, 0];
        p[a] = s;
        p[(a + 1) % 3] = i;
        p[(a + 2) % 3] = j;
        out.push({ p: p, n: F.n.slice(), ch: '' });
      }
    });
    if (letters) out.forEach((st, i) => { st.ch = letters[i] || ''; });
    return out;
  }

  const clone = st => st.map(s => ({ p: s.p.slice(), n: s.n.slice(), ch: s.ch }));

  /* A turn rotates every sticker in the layer — the nine on the face plus the
     twelve around its rim, which is exactly "p's component along this axis
     equals this face's sign". Nothing else needs saying. */
  function applyMove(state, move) {
    const f = move[0], prime = move.length > 1;
    const F = FACES[f], a = axisOf(f), s = signOf(f);
    const turn = prime ? v => F.cw(F.cw(F.cw(v))) : F.cw;
    state.forEach(st => {
      if (st.p[a] !== s) return;
      st.p = turn(st.p);
      st.n = turn(st.n);
    });
    return state;
  }
  const invert = m => (m.length > 1 ? m[0] : m + "'");
  const inverseOf = seq => seq.slice().reverse().map(invert);

  /* The letters currently sitting in a face's slots, in reading order. */
  function faceLetters(state, f) {
    const out = new Array(9).fill('');
    state.forEach(st => {
      if (st.n[0] === FACES[f].n[0] && st.n[1] === FACES[f].n[1] && st.n[2] === FACES[f].n[2]) {
        out[slotOf(f, st.p)] = st.ch;
      }
    });
    return out;
  }
  const readWord = (state, f, len) => faceLetters(state, f).slice(0, len).join('');

  /* ---------- letters ----------
     Filler is frequency-weighted rather than uniform: a face of QXZJ reads as
     noise, and part of the pleasure is that the cube looks like it might spell
     something anywhere. */
  const FILLER = 'EEEEEETTTTAAAAOOOOIIIINNNNSSSSHHHRRRDDLLCCUUMMWWFFGGYYPPBBVKJ';

  /* Deliberately plain, high-frequency words — the puzzle is spatial, so the
     vocabulary should never be the obstacle. Three rungs, three lengths. */
  const WORDS = {
    4: ('ABLE ACID AREA ARMY AWAY BABY BACK BALL BAND BANK BASE BEAR BEAT BELL BEST BIRD BLUE BOAT BODY BONE BOOK BORN BOSS ' +
        'CAGE CAKE CALL CALM CARD CARE CASE CASH CITY CLUB COAL COAT COLD COOK COOL COPY CORN DARK DATE DAWN DEAL DEEP DESK ' +
        'DISH DOOR DOWN DRAW DROP DUST EARN EAST EASY EDGE FACE FACT FAIR FALL FARM FAST FEAR FEED FEEL FILE FILM FIND FINE ' +
        'FIRE FISH FIVE FLAG FLAT FLOW FOOD FOOT FORM FOUR FREE FROG FUEL FULL GAME GATE GIFT GIRL GIVE GLAD GOAL GOLD GOOD ' +
        'GRAY GROW HAIR HALF HALL HAND HARD HEAD HEAR HEAT HELP HERO HIDE HIGH HILL HOLD HOLE HOME HOPE HOUR IDEA IRON ITEM ' +
        'JOIN JUMP KEEP KIND KING KNEE KNOW LACK LAKE LAMP LAND LATE LEAD LEAF LEFT LIFE LIFT LIKE LINE LION LIST LIVE LOAD ' +
        'LOCK LONG LOOK LOSE LOUD LOVE LUCK MAIL MAIN MAKE MANY MARK MASK MEAL MEAN MEAT MEET MILD MILE MILK MIND MINE MISS ' +
        'MOON MORE MOST MOVE MUCH NAME NEAR NECK NEED NEST NEWS NEXT NICE NOTE OPEN PACK PAGE PAIN PAIR PARK PART PAST PATH ' +
        'PICK PINK PLAN PLAY PLUS POEM POOL POOR PORT POST PULL PURE PUSH RACE RAIN RATE READ REAL REST RICE RICH RIDE RING ' +
        'RISE RISK ROAD ROCK ROLE ROLL ROOF ROOM ROOT ROSE RULE RUSH SAFE SAIL SALT SAME SAND SAVE SEAT SEED SEEK SEEM SELL ' +
        'SEND SHIP SHOE SHOP SHOT SHOW SICK SIDE SIGN SILK SING SITE SIZE SKIN SLOW SNOW SOFT SOIL SOLD SONG SOON SORT SOUL ' +
        'SOUP SPOT STAR STAY STEP STOP SUCH SUIT SURE SWIM TAKE TALE TALK TALL TANK TAPE TASK TEAM TEAR TELL TEND TERM TEST ' +
        'TEXT THAN THAT THEM THEN THEY THIN THIS TIDE TIME TINY TIRE TONE TOOL TOUR TOWN TREE TRIP TRUE TUNE TURN TWIN TYPE ' +
        'UNIT UPON USED USER VAST VERY VIEW VOTE WAGE WAIT WAKE WALK WALL WANT WARM WASH WAVE WEAK WEAR WEEK WELL WEST WHAT ' +
        'WHEN WIDE WIFE WILD WILL WIND WINE WING WIRE WISE WISH WOOD WORD WORE WORK YARD YEAR ZERO ZONE').split(' '),
    5: ('ABOUT ABOVE ACTOR ADMIT ADULT AFTER AGAIN AGENT AGREE AHEAD ALARM ALBUM ALIVE ALLOW ALONE ALONG ANGEL ANGER ANGLE ' +
        'APART APPLE APPLY ARENA ARGUE ARISE ARRAY ASIDE ASSET AUDIO AVOID AWARD AWARE BADLY BAKER BASIC BEACH BEGAN BEGIN ' +
        'BEING BELOW BENCH BIRTH BLACK BLADE BLAME BLANK BLAST BLEND BLIND BLOCK BLOOD BOARD BOAST BONUS BOOST BOOTH BOUND ' +
        'BRAIN BRAND BRAVE BREAD BREAK BRICK BRIEF BRING BROAD BROWN BRUSH BUILD BUILT BUNCH BURST CABIN CABLE CANDY CARGO ' +
        'CARRY CATCH CAUSE CHAIN CHAIR CHALK CHARM CHART CHASE CHEAP CHECK CHEST CHIEF CHILD CHINA CHOSE CIVIL CLAIM CLASS ' +
        'CLEAN CLEAR CLERK CLICK CLIMB CLOCK CLOSE CLOTH CLOUD COACH COAST COUNT COURT COVER CRAFT CRASH CRAZY CREAM CRIME ' +
        'CROSS CROWD CROWN CURVE CYCLE DAILY DANCE DEATH DELAY DEPTH DOING DOUBT DOZEN DRAFT DRAMA DRANK DREAM DRESS DRIED ' +
        'DRINK DRIVE DROVE DYING EAGER EARLY EARTH EIGHT ELITE EMPTY ENEMY ENJOY ENTER ENTRY EQUAL ERROR EVENT EVERY EXACT ' +
        'EXIST EXTRA FAITH FALSE FAULT FENCE FEVER FIELD FIFTH FIFTY FIGHT FINAL FIRST FLAME FLASH FLEET FLOAT FLOOR FLOUR ' +
        'FLUID FOCUS FORCE FORTH FORTY FORUM FOUND FRAME FRANK FRESH FRONT FRUIT FULLY FUNNY GIANT GIVEN GLASS GLOBE GLORY ' +
        'GRACE GRADE GRAIN GRAND GRANT GRASS GRAVE GREAT GREEN GREET GROSS GROUP GROWN GUARD GUESS GUEST GUIDE HABIT HAPPY ' +
        'HARSH HEART HEAVY HENCE HORSE HOTEL HOUSE HUMAN HUMOR IDEAL IMAGE IMPLY INDEX INNER INPUT ISSUE IVORY JOINT JUDGE ' +
        'KNIFE KNOCK KNOWN LABEL LARGE LASER LATER LAUGH LAYER LEARN LEASE LEAST LEAVE LEGAL LEMON LEVEL LIGHT LIMIT LOCAL ' +
        'LOGIC LOOSE LOWER LOYAL LUCKY LUNCH LYING MAGIC MAJOR MAKER MARCH MATCH MAYBE MAYOR MEANT MEDAL MEDIA MERCY MERIT ' +
        'METAL METER MIGHT MINOR MINUS MIXED MODEL MONEY MONTH MORAL MOTOR MOUNT MOUSE MOUTH MOVIE MUSIC NAKED NERVE NEVER ' +
        'NEWLY NIGHT NOBLE NOISE NORTH NOVEL NURSE OCCUR OCEAN OFFER OFTEN ORDER OTHER OUGHT OUTER OWNER PAINT PANEL PAPER ' +
        'PARTY PEACE PEARL PHASE PHONE PHOTO PIANO PIECE PILOT PITCH PLACE PLAIN PLANE PLANT PLATE POINT POUND POWER PRESS ' +
        'PRICE PRIDE PRIME PRINT PRIOR PRIZE PROOF PROUD PROVE QUEEN QUICK QUIET QUITE RADIO RAISE RANGE RAPID RATIO REACH ' +
        'READY REALM REBEL REFER RELAX REPLY RIGHT RIVAL RIVER ROBIN ROMAN ROUGH ROUND ROUTE ROYAL RURAL SAFER SALAD SCALE ' +
        'SCENE SCOPE SCORE SENSE SERVE SEVEN SHADE SHAKE SHALL SHAPE SHARE SHARP SHEEP SHEET SHELF SHELL SHIFT SHINE SHIRT ' +
        'SHOCK SHOOT SHORE SHORT SHOWN SIGHT SILLY SINCE SIXTH SIXTY SKILL SLEEP SLIDE SMALL SMART SMILE SMOKE SNAKE SOLAR ' +
        'SOLID SOLVE SORRY SOUND SOUTH SPACE SPARE SPEAK SPEED SPELL SPEND SPENT SPINE SPLIT SPOKE SPORT STAFF STAGE STAKE ' +
        'STAND START STATE STEAM STEEL STEEP STEER STICK STILL STOCK STONE STOOD STORE STORM STORY STRIP STUCK STUDY STUFF ' +
        'STYLE SUGAR SUITE SUPER SWEET TABLE TASTE TEACH TEETH TERMS THANK THEFT THEIR THEME THERE THESE THICK THING THINK ' +
        'THIRD THOSE THREE THREW THROW TIGER TIGHT TIMER TIRED TITLE TODAY TOKEN TOTAL TOUCH TOUGH TOWEL TOWER TRACK TRADE ' +
        'TRAIL TRAIN TREAT TREND TRIAL TRIBE TRICK TRIED TRUCK TRULY TRUST TRUTH TWICE TWIST UNCLE UNDER UNION UNITE UNITY ' +
        'UNTIL UPPER UPSET URBAN USAGE USUAL VALID VALUE VIDEO VIRUS VISIT VITAL VOICE WASTE WATCH WATER WHEEL WHERE WHICH ' +
        'WHILE WHITE WHOLE WHOSE WOMAN WOMEN WORLD WORRY WORSE WORST WORTH WOULD WRITE WRONG WROTE YIELD YOUNG YOURS ' +
        'YOUTH').split(' '),
    6: ('ACCEPT ACCESS ACROSS ACTION ACTIVE ACTUAL ADVICE ADVISE AFFECT AFFORD AFRAID AGENCY AGENDA ALMOST ALWAYS AMOUNT ' +
        'ANIMAL ANNUAL ANSWER ANYONE ANYWAY APPEAL APPEAR AROUND ARRIVE ARTIST ASPECT ASSESS ASSIST ASSUME ATTACK ATTEND ' +
        'AUGUST AUTHOR AUTUMN AVENUE BACKED BANNER BARELY BARREL BASKET BATTLE BEAUTY BECAME BECOME BEFORE BEHALF BEHAVE ' +
        'BEHIND BELIEF BELONG BENEFIT BESIDE BETTER BEYOND BINARY BISHOP BOTTLE BOTTOM BOUGHT BRANCH BREATH BRIDGE BRIGHT ' +
        'BROKEN BUDGET BUFFER BUREAU BUTTON CAMERA CANCEL CANDLE CANNOT CANVAS CARBON CAREER CARPET CARROT CASTLE CASUAL ' +
        'CAUGHT CAUSED CENTER CENTRE CHANCE CHANGE CHARGE CHOICE CHOOSE CHOSEN CHURCH CIRCLE CLIENT CLOSED CLOSER COFFEE ' +
        'COLLAR COLUMN COMBAT COMEDY COMING COMMON COPPER CORNER COTTON COUNTY COUPLE COURSE COUSIN CREATE CREDIT CRISIS ' +
        'CRITIC CROWD CUSTOM DAMAGE DANGER DEALER DEBATE DECADE DECIDE DEFEAT DEFEND DEFINE DEGREE DELETE DEMAND DEPEND ' +
        'DEPUTY DESERT DESIGN DESIRE DETAIL DETECT DEVICE DIRECT DIVIDE DOCTOR DOLLAR DOMAIN DOUBLE DRIVEN DURING EASILY ' +
        'EASTER EDITOR EFFECT EFFORT EIGHTH EITHER ELEVEN EMPIRE EMPLOY ENABLE ENDING ENERGY ENGAGE ENGINE ENOUGH ENSURE ' +
        'ENTIRE ENTITY EQUITY ESCAPE ESTATE ETHNIC EXCEED EXCEPT EXCESS EXCUSE EXPAND EXPECT EXPERT EXPORT EXTEND EXTENT ' +
        'FABRIC FACING FACTOR FAILED FAIRLY FALLEN FAMILY FAMOUS FARMER FASTER FATHER FELLOW FEMALE FIGURE FILING FINGER ' +
        'FINISH FISCAL FLIGHT FLOWER FLYING FOLLOW FOREST FORGET FORMAL FORMAT FORMER FOSTER FOUGHT FOURTH FRENCH FRIDAY ' +
        'FRIEND FROZEN FUTURE GARDEN GATHER GENDER GENTLE GLOBAL GOLDEN GOTTEN GOVERN GROUND GROUPS GROWTH GUILTY HANDLE ' +
        'HAPPEN HARDLY HEADED HEALTH HEIGHT HIDDEN HOLDER HONEST HORROR HOTELS HOUSES HUMBLE HUNGRY HUNTER IMPACT IMPORT ' +
        'INCOME INDEED INJURY INSIDE INTEND INTENT INVENT INVEST ISLAND ITSELF JOINED JUNIOR JUSTICE KEEPER KERNEL KIDNEY ' +
        'LABOUR LADDER LATTER LAUNCH LAWYER LEADER LEAGUE LEAVES LEGACY LEGEND LENGTH LESSON LETTER LIGHTS LIKELY LINKED ' +
        'LIQUID LISTEN LITTLE LIVING LOCATE LOCKED LONGER LOOKED LOVELY LOVING LUXURY MAINLY MAKING MANAGE MANNER MANUAL ' +
        'MARBLE MARGIN MARINE MARKED MARKET MASTER MATTER MATURE MEDIUM MEMBER MEMORY MENTAL MERELY MERGER METHOD MIDDLE ' +
        'MILLER MINING MINUTE MIRROR MOBILE MODERN MODEST MODULE MOMENT MONDAY MONKEY MONTHS MORTAL MOSTLY MOTHER MOTION ' +
        'MOVING MURDER MUSEUM MUTUAL MYSELF NARROW NATION NATIVE NATURE NEARBY NEARLY NEEDLE NEPHEW NERVES NEWEST NIGHTS ' +
        'NOBODY NORMAL NOTICE NOTION NUMBER OBJECT OBTAIN OFFICE OFFSET ONLINE OPPOSE OPTION ORANGE ORDERS ORIGIN OTHERS ' +
        'OUTPUT OUTSET OXFORD PALACE PARENT PARTLY PATENT PATROL PAYING PEOPLE PERIOD PERMIT PERSON PHRASE PICKED PIECES ' +
        'PLACES PLANET PLAYER PLEASE PLENTY POCKET POETRY POLICE POLICY PRAYER PREFER PRETTY PRINCE PRISON PROFIT PROPER ' +
        'PROVEN PUBLIC PURPLE PURSUE PUZZLE RABBIT RADIUS RAISED RANDOM RARELY RATHER RATING READER REALLY REASON RECALL ' +
        'RECENT RECORD REDUCE REFORM REGARD REGION REGRET REJECT RELATE RELIEF REMAIN REMOTE REMOVE REPAIR REPEAT REPORT ' +
        'RESCUE RESIST RESORT RESULT RETAIL RETAIN RETURN REVEAL REVIEW REWARD RIDING RISING ROBUST ROLLED RULING RUNNER ' +
        'RUNNING SAFETY SALARY SAMPLE SAVING SAYING SCHEME SCHOOL SCREEN SEARCH SEASON SECOND SECRET SECTOR SECURE SEEING ' +
        'SELECT SELLER SENIOR SERIES SERVED SETTLE SEVERE SHADOW SHAPED SHARED SHIELD SHIFT SHOULD SHOWED SHOWER SIGNAL ' +
        'SILENT SILVER SIMPLE SIMPLY SINGER SINGLE SISTER SLIGHT SMOOTH SOCIAL SOCKET SOFTLY SOLELY SOLVED SOURCE SOVIET ' +
        'SPEAKS SPIRIT SPOKEN SPREAD SPRING SQUARE STABLE STATED STATIC STATUE STATUS STEADY STOLEN STRAIN STRAND STREAM ' +
        'STREET STRESS STRICT STRIKE STRING STRONG STRUCK STUDIO SUBMIT SUDDEN SUFFER SUMMER SUMMIT SUNDAY SUPPLY SURELY ' +
        'SURVEY SWITCH SYMBOL SYSTEM TAKING TALENT TARGET TAUGHT TEMPLE TENDER TENNIS THEORY THIRTY THOUGH THREAD THREAT ' +
        'THROWN TICKET TIMBER TIMELY TIMING TISSUE TITLED TOWARD TRAVEL TREATY TRENDS TRIBAL TRIPLE TROPHY TRUTHS TRYING ' +
        'TUNNEL TURNED TWELVE TWENTY UNABLE UNIQUE UNITED UNLESS UNLIKE UPDATE USEFUL VALLEY VARIED VENDOR VERSUS VESSEL ' +
        'VIABLE VICTIM VISION VISUAL VOLUME VOTING WAITED WALKED WALLET WANTED WARMTH WARNED WEALTH WEEKLY WEIGHT WHEELS ' +
        'WHOLLY WINDOW WINNER WINTER WISDOM WITHIN WONDER WOODEN WORKER WORTHY WRITER YELLOW').split(' '),
  };

  /* ---------- scrambling ----------
     Two hygiene rules, both about not wasting the player's patience: never
     immediately undo the previous move (the depth would be a lie), and never
     turn the same face twice in a row (that is one move dressed as two). */
  function scramble(state, depth, rng) {
    const seq = [];
    let last = '';
    for (let i = 0; i < depth; i++) {
      let m;
      do { m = pick(MOVES, rng); } while (m[0] === last);
      last = m[0];
      seq.push(m);
      applyMove(state, m);
    }
    return seq;
  }

  /* ---------- one rung ----------
     Build the answer first, then walk away from it. `depth` is therefore a
     hard ceiling on the solution length, not an estimate. */
  function buildRung(word, depth, rng) {
    const L = word.length;
    for (let attempt = 0; attempt < 40; attempt++) {
      const letters = [];
      for (let i = 0; i < 54; i++) letters.push(pick(FILLER, rng));
      const solved = solvedShell(letters);
      /* seat the word in the front face's first L reading slots */
      solved.forEach(st => {
        if (st.n[2] !== 1) return;
        const s = slotOf('F', st.p);
        if (s < L) st.ch = word[s];
      });
      const start = clone(solved);
      const seq = scramble(start, depth, rng);
      /* a scramble that happens to leave the word standing is not a puzzle */
      if (readWord(start, 'F', L) === word) continue;
      return { word: word, len: L, depth: depth, start: start, solution: inverseOf(seq) };
    }
    return null;
  }

  /* ---------- the date is the puzzle ---------- */
  const ID_RE = /^turnspell-(\d{4}-\d{2}-\d{2})$/;
  const idFor = iso => 'turnspell-' + iso;
  const parseId = id => { const m = ID_RE.exec(String(id || '')); return m ? { date: m[1] } : null; };
  function todayISO(d) {
    d = d || new Date();
    return d.getFullYear() + '-' + String(d.getMonth() + 1).padStart(2, '0') +
           '-' + String(d.getDate()).padStart(2, '0');
  }

  /* Three rungs, lengths 4/5/6 at depths 2/3/4. The ramp is deliberately
     gentle: rung one is really a tutorial you can solve by staring at it, and
     rung three still cannot need more than four turns. */
  const LADDER = [{ len: 4, depth: 2 }, { len: 5, depth: 3 }, { len: 6, depth: 4 }];

  function forDate(iso) {
    const rng = mulberry32(hashSeed('lat-turnspell:' + iso));
    const rungs = [];
    const used = {};
    LADDER.forEach(spec => {
      let w, guard = 0;
      do { w = pick(WORDS[spec.len], rng); } while (used[w] && ++guard < 20);
      used[w] = true;
      const r = buildRung(w, spec.depth, rng);
      if (r) rungs.push(r);
    });
    return { id: idFor(iso), date: iso, rungs: rungs };
  }

  root.TURNSPELL = {
    FACES: FACES, FACE_IDS: FACE_IDS, MOVES: MOVES, LADDER: LADDER,
    slotOf: slotOf, axisOf: axisOf, signOf: signOf,
    applyMove: applyMove, invert: invert, inverseOf: inverseOf, clone: clone,
    faceLetters: faceLetters, readWord: readWord,
    forDate: forDate, todayISO: todayISO, idFor: idFor, parseId: parseId,
    WORDS: WORDS,
  };
})(typeof window !== 'undefined' ? window : globalThis);

if (typeof module !== 'undefined' && module.exports) module.exports = globalThis.TURNSPELL;
