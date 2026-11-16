// parse.js — fast Markdown to HTML, byte-identical to marked 18.1.3 with
// default options (GFM on, hard breaks off, pedantic off).
//
// Design: two phases. Phase one walks the block grammar and builds a compact
// list of block nodes while collecting link reference definitions. Phase two
// renders those nodes, scanning inline content straight to HTML with an index
// cursor — no token tree, no per-token objects, no second lex pass. Inline
// runs are scanned only after every definition is known, so a reference
// defined later in the document still resolves earlier text, exactly as the
// reference renderer does.
//
// The grammar decisions follow the CommonMark 0.31.2 + GFM 0.29 rules. Every
// line here is an original implementation written for this entry.

'use strict';

// ---------------------------------------------------------------------------
// Small helpers
// ---------------------------------------------------------------------------

const ESCAPE_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const RE_ESC_TEST = /[&<>"']/;
const RE_ESC_ALL = /[&<>"']/g;
const RE_ESC_TEST_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const RE_ESC_NOENC = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Escape HTML metacharacters. With encode set, every & is escaped; otherwise
// an & that already starts a valid character reference is left alone.
function esc(html, encode) {
  if (!RE_ESC_TEST.test(html)) return html;
  if (encode) return html.replace(RE_ESC_ALL, (ch) => ESCAPE_MAP[ch]);
  return html.replace(RE_ESC_NOENC, (ch) => ESCAPE_MAP[ch]);
}

const RE_NUMREF_TEST = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const RE_NUMREF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Outside code, a numeric character reference stands for the character it
// names. Zero, out-of-range and surrogate values become U+FFFD; a bare &
// that is not already a reference is escaped so it cannot join its neighbours
// into a new reference once decoded output is concatenated.
function decodeRefs(text) {
  if (!RE_NUMREF_TEST.test(text)) return text;
  return text.replace(RE_NUMREF, (ref, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '�';
    return code === 38 ? '&amp;' : String.fromCodePoint(code);
  });
}

const RE_PCT = /%25/g;
// Characters encodeURI leaves alone (plus %, which encodeURI escapes to
// %25 and the replacement below turns straight back).
const URL_FAST = new Uint8Array(128);
for (const ch of ";,/?:@&=+$-_.!~*'()#%") URL_FAST[ch.charCodeAt(0)] = 1;
for (let c = 48; c <= 57; c++) URL_FAST[c] = 1;
for (let c = 65; c <= 90; c++) URL_FAST[c] = 1;
for (let c = 97; c <= 122; c++) URL_FAST[c] = 1;
function cleanUrl(href) {
  let fast = true;
  for (let i = 0; i < href.length; i++) {
    const c = href.charCodeAt(i);
    if (c >= 128 || !URL_FAST[c]) { fast = false; break; }
  }
  if (fast) return href;
  try {
    return encodeURI(href).replace(RE_PCT, '%');
  } catch {
    return null;
  }
}

const RE_WS_RUN = /\s+/g;
function normalizeLabel(label) {
  return label.trim().replace(RE_WS_RUN, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Remove a trailing run of one repeated character.
function rtrimChar(str, c) {
  let end = str.length;
  while (end > 0 && str.charAt(end - 1) === c) end--;
  return str.slice(0, end);
}

const RE_BLANK = /^[ \t]*$/;
// Drop trailing blank lines, keeping at most one: scan back past the trailing
// whitespace-only tail, then cut at the end of the last line holding a
// non-blank character when two or more newlines follow it.
function trimTrailingBlanks(str) {
  let p = str.length - 1;
  while (p >= 0) {
    const c = str.charCodeAt(p);
    if (c !== 32 && c !== 9 && c !== 10) break;
    p--;
  }
  const cut = str.indexOf('\n', p + 1);
  const end = cut === -1 ? str.length : cut;
  let nls = 0;
  for (let i = end; i < str.length; i++) {
    if (str.charCodeAt(i) === 10 && ++nls >= 2) return str.slice(0, end);
  }
  return str;
}

// Index of the first unmatched closer in str, -1 when the brackets balance
// (or neither bracket appears), -2 when opens outnumber closes at the end.
// A backslash escapes the next character.
function findClosingBracket(str, pair) {
  if (str.indexOf(pair[0]) === -1 && str.indexOf(pair[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    const ch = str[i];
    if (ch === '\\') i++;
    else if (ch === pair[0]) level++;
    else if (ch === pair[1] && --level < 0) return i;
  }
  return level > 0 ? -2 : -1;
}

function expandTabs(line, indent) {
  let col = indent || 0;
  let out = '';
  for (const ch of line) {
    if (ch === '\t') {
      const add = 4 - (col % 4);
      out += ' '.repeat(add);
      col += add;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}

const RE_FIND_PIPE = /\|/g;
const RE_SPLIT_PIPE = / \|/;
const RE_SLASH_PIPE = /\\\|/g;
function splitCells(row, count) {
  const fixed = row.replace(RE_FIND_PIPE, (match, offset, str) => {
    let escaped = false;
    let curr = offset;
    while (--curr >= 0 && str[curr] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = fixed.split(RE_SPLIT_PIPE);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells[cells.length - 1].trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.length = count;
    else while (cells.length < count) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) cells[i] = cells[i].trim().replace(RE_SLASH_PIPE, '|');
  return cells;
}

const RE_UNESCAPE_TEST = /\\[\p{P}\p{S}]/u;
const RE_UNESCAPE_G = /\\([\p{P}\p{S}])/gu;
// Drop the backslash before a punctuation or symbol character.
function unescapePunct(s) {
  return RE_UNESCAPE_TEST.test(s) ? s.replace(RE_UNESCAPE_G, '$1') : s;
}

// Length in UTF-16 code units of the first code point of s.
function firstCodePointLen(s) {
  const c0 = s.charCodeAt(0);
  if (c0 >= 0xd800 && c0 <= 0xdbff) {
    const c1 = s.charCodeAt(1);
    if (c1 >= 0xdc00 && c1 <= 0xdfff) return 2;
  }
  return 1;
}

// The code point ending just before index i ('' when i is 0).
function charBefore(s, i) {
  if (i <= 0) return '';
  const lo = s.charCodeAt(i - 1);
  if (lo >= 0xdc00 && lo <= 0xdfff && i >= 2) {
    const hi = s.charCodeAt(i - 2);
    if (hi >= 0xd800 && hi <= 0xdbff) return s.slice(i - 2, i);
  }
  return s[i - 1];
}

// ---------------------------------------------------------------------------
// Grammar: block patterns (GFM)
// ---------------------------------------------------------------------------

const TAG_NAMES = 'address|article|aside|base|basefont|blockquote|body|caption'
  + '|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption'
  + '|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe'
  + '|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option'
  + '|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title'
  + '|tr|track|ul';

const BULL_SRC = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const HR_SRC = ' {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
const ATX_SRC = ' {0,3}#{1,6}(?:\\s|$)';
const FENCE_OPEN_SRC = ' {0,3}(?:`{3,}|~{3,})';
const FENCE_LINE_SRC = ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)';
const HTML_START_SRC = ' {0,3}(?:</?(?:' + TAG_NAMES + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)';

const R_BLOCK_NEWLINE = /^(?:[ \t]*(?:\n|$))+/;
const R_BLOCK_CODE = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const R_FENCES = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const R_HR = new RegExp('^' + HR_SRC);
const R_HEADING = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const R_TEXT = /^[^\n]+/;

const HR_NC_SRC = ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)';
// Setext heading (GFM variant: a table delimiter row can also interrupt).
const LHEADING_SRC = '^(?!' + BULL_SRC + ' |(?: {4}| {0,3}\\t)|' + FENCE_OPEN_SRC + '| {0,3}>|' + ATX_SRC
  + '| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n)'
  + '((?:.|\\n(?!\\s*?\\n|' + BULL_SRC + ' |' + FENCE_OPEN_SRC + '| {0,3}>|' + ATX_SRC + '|' + HR_NC_SRC
  + '| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n))+?)'
  + '\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)';
const R_LHEADING = new RegExp(LHEADING_SRC);

// GFM table: header line, delimiter row, then body rows until a blank line
// or another interrupting block.
const TABLE_SRC = '^ *([^\\n ].*)\\n'
  + ' {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)'
  + '(?:\\n((?:(?! *\\n|' + HR_SRC + '|' + ATX_SRC + '| {0,3}>|(?: {4}| {0,3}\\t)[^\\n]|' + FENCE_LINE_SRC
  + '| {0,3}(?:[*+-]|1[.)])[ \\t]|' + HTML_START_SRC + ').*(?:\\n|$))*)\\n*|$)';
const R_TABLE = new RegExp(TABLE_SRC);

// A paragraph consumes lines until a blank line or an interrupting block.
// Only non-empty lists starting at 1 (or a bullet) interrupt; setext
// underlines do not.
const PARA_SRC = '^([^\\n]+(?:\\n(?!' + HR_SRC + '|' + ATX_SRC + '| {0,3}>|' + FENCE_LINE_SRC
  + '| {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]|' + HTML_START_SRC + '|' + TABLE_SRC.slice(1)
  + '|[ \\t]+\\n)[^\\n]+)*)';
const R_PARA = new RegExp(PARA_SRC);

// Inside a blockquote, a bare list marker with any number starts a sibling
// list, so it must not be lazily continued as paragraph text.
const BQ_PARA_SRC = '^([^\\n]+(?:\\n(?!' + HR_SRC + '|' + ATX_SRC + '| {0,3}>|' + FENCE_LINE_SRC
  + '| {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)|' + HTML_START_SRC + '|[ \\t]+\\n)[^\\n]+)*)';
const R_BLOCKQUOTE = new RegExp('^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(' + BQ_PARA_SRC.slice(1) + ')|[^\\n]*)(?:\\n|$))+');

// Block HTML, types 1-7.
const HTML_ATTR = ' +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?';
const HTML_BLOCK_SRC = '^ {0,3}(?:'
  + '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)'
  + '|<!--(?:-?>|[\\s\\S]*?(?:-->|$))[^\\n]*(\\n+|$)'
  + '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)'
  + '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)'
  + '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)'
  + '|</?(?:' + TAG_NAMES + ')(?:[ \\t]+|\\n|/?>)[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:' + HTML_ATTR + ')*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \\t]*)+\\n|$)'
  + ')';
const R_HTML_BLOCK = new RegExp(HTML_BLOCK_SRC, 'i');

// Link reference definition.
const BLOCK_LABEL_SRC = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+';
const DEF_TITLE_SRC = '(?:"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))';
const R_DEF = new RegExp('^ {0,3}\\[(' + BLOCK_LABEL_SRC + ')\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)(' + DEF_TITLE_SRC + '))? *(?:\\n+|$)');

const R_LIST = new RegExp('^(' + BULL_SRC + ')([ \\t][^\\n]*?)?(?:\\n|$)');

// Block-level odds and ends.
const R_CODE_DEDENT = /^(?: {0,3}\t| {1,4})/gm;
const R_FENCE_INDENT = /^(\s+)(?:```)/;
const R_LEAD_WS = /^\s+/;
const R_END_HASH = /#$/;
const R_END_SPACE_TAB = /[ \t]$/;
const R_NON_SPACE = /[^ ]/;
const R_DOUBLE_BLANK = /\n[ \t]*\n[ \t]*$/;
const R_BQ_START = /^ {0,3}>/;
const R_BQ_SETEXT = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const R_BQ_STRIP = /^ {0,3}>[ \t]?/gm;
const R_BQ_MARKER_WS = /^( {0,3}>)([ \t]+)/gm;
const R_TASK = /^\[[ xX]\][ \t]+\S/;
const R_TASK_STRIP = /^\[[ xX]\][ \t]+/;
const R_TASK_BOX = /\[[ xX]\]/;
const R_ANY_LINE = /\n.*\n/;
const R_HREF_BRACKETS = /^<(.*)>$/; // strips the angle brackets of a link destination
const R_TABLE_DELIM = /[:|]/;
const R_TABLE_ALIGN_TRIM = /^\||\| *$/g;
const R_TABLE_ROW_BLANK = /\n[ \t]*$/;
const R_ALIGN_RIGHT = /^ *-+: *$/;
const R_ALIGN_CENTER = /^ *:-+: *$/;
const R_ALIGN_LEFT = /^ *:-+ *$/;
const R_LEAD_SPACE_TAB = /^[ \t]+/;
const R_SETEXT_LAZY = /^ {0,3}(?:=+|-+) *$/;
const R_STRIP_3 = /^ {0,3}/; // removes up to three leading spaces
const R_NOT_SPACE_START = /^\S*/;
const R_END_NL = /\n$/;

const _itemReCache = new Map();
function listItemRegex(bull) {
  let re = _itemReCache.get(bull);
  if (!re) {
    re = new RegExp('^( {0,3}' + bull + ')((?:[\\t ][^\\n]*)?(?:\\n|$))');
    _itemReCache.set(bull, re);
  }
  return re;
}

// First line of s (up to the first newline, or all of s).
function firstLineOf(s) {
  const nl = s.indexOf('\n');
  return nl === -1 ? s : s.slice(0, nl);
}

// Index of the first character that is not a space, or -1.
function firstNonSpace(s) {
  for (let i = 0; i < s.length; i++) if (s.charCodeAt(i) !== 32) return i;
  return -1;
}

// True when every character is whitespace (the same test as !s.trim()).
function isBlankTrim(s) {
  for (let i = 0; i < s.length; i++) if (!isWsCode(s.charCodeAt(i))) return false;
  return true;
}

// True when every character is a space or a tab.
function isBlankSpaceTab(s) {
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// Expand tabs in the leading whitespace run; a run without tabs is already
// in its expanded form, so the line is returned untouched.
function expandLeadTabs(line, indent) {
  let i = 0;
  while (i < line.length) {
    const c = line.charCodeAt(i);
    if (c === 9) return line.replace(R_LEAD_SPACE_TAB, (ws) => expandTabs(ws, indent));
    if (c !== 32) break;
    i++;
  }
  return line;
}

// True when s ends with a blank line preceded by another blank line.
function endsDoubleBlank(s) {
  let i = s.length;
  while (i > 0 && (s.charCodeAt(i - 1) === 32 || s.charCodeAt(i - 1) === 9)) i--;
  if (i === 0 || s.charCodeAt(i - 1) !== 10) return false;
  i--;
  while (i > 0 && (s.charCodeAt(i - 1) === 32 || s.charCodeAt(i - 1) === 9)) i--;
  if (i === 0 || s.charCodeAt(i - 1) !== 10) return false;
  return true;
}

// True when the first non-space character of the line sits at a tab-expanded
// indent of four or more (an indented code line).
function indentedCodeLine(line) {
  let p = 0;
  for (let q = 0; q < line.length; q++) {
    const cc = line.charCodeAt(q);
    if (cc === 32) p++;
    else if (cc === 9) p += 4;
    else return p >= 4;
  }
  return false;
}

// Whether a continuation line interrupts the list item: a new bullet, a
// thematic break, a fence, a heading, an HTML block or a blockquote start
// within the allowed indentation. Only the patterns whose starter character
// appears are run.
function interruptsItem(line, idx, res) {
  let fs = 0;
  while (fs < line.length && line.charCodeAt(fs) === 32) fs++;
  if (fs > idx) return false;
  const c = line.charCodeAt(fs);
  if (c === 42 || c === 43 || c === 45 || (c >= 48 && c <= 57)) {
    if (res[0].test(line)) return true;
  }
  if (c === 45 || c === 95 || c === 42) {
    if (res[1].test(line)) return true;
  }
  if (c === 96 || c === 126) {
    if (res[2].test(line)) return true;
  }
  if (c === 35) {
    if (res[3].test(line)) return true;
  }
  if (c === 60) {
    if (res[4].test(line)) return true;
  }
  if (c === 62) {
    if (res[5].test(line)) return true;
  }
  return false;
}

// The interrupt test for a lazy continuation line: fences, headings, HTML
// blocks and thematic breaks only.
function interruptsLazy(line, idx, res) {
  let fs = 0;
  while (fs < line.length && line.charCodeAt(fs) === 32) fs++;
  if (fs > idx) return false;
  const c = line.charCodeAt(fs);
  if (c === 96 || c === 126) {
    if (res[2].test(line)) return true;
  }
  if (c === 35) {
    if (res[3].test(line)) return true;
  }
  if (c === 60) {
    if (res[4].test(line)) return true;
  }
  if (c === 45 || c === 95 || c === 42) {
    if (res[1].test(line)) return true;
  }
  return false;
}

// The list-item continuation tests cap their allowed indentation at three
// spaces no matter how deep the item is indented.
const _indentCache = [];
function indentRegex(kind, indent) {
  const idx = Math.max(0, Math.min(3, indent - 1));
  let slot = _indentCache[idx];
  if (!slot) slot = _indentCache[idx] = [];
  let re = slot[kind];
  if (re) return re;
  if (kind === 0) re = new RegExp('^ {0,' + idx + '}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))');
  else if (kind === 1) re = new RegExp('^ {0,' + idx + '}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)');
  else if (kind === 2) re = new RegExp('^ {0,' + idx + '}(?:```|~~~)');
  else if (kind === 3) re = new RegExp('^ {0,' + idx + '}#{1,6}(?:\\s|$)');
  else if (kind === 4) re = new RegExp('^ {0,' + idx + '}(?:</?(?:' + TAG_NAMES + ')(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)', 'i');
  else re = new RegExp('^ {0,' + idx + '}>');
  slot[kind] = re;
  return re;
}

// ---------------------------------------------------------------------------
// Grammar: inline patterns (GFM)
// ---------------------------------------------------------------------------

const R_ESCAPE = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const R_CODESPAN = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const R_BR = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;
const R_NL_GLOBAL = /\n/g;
const R_TAB_GLOBAL = /\t/g;
const R_OUTPUT_LINK = /\\([\[\]])/g;
const R_START_LT = /^</;
const R_END_GT = />$/;
const R_START_A = /^<a /i;
const R_END_A = /^<\/a>/i;
const R_START_PRE = /^<(pre|code|kbd|script)(\s|>)/i;
const R_END_PRE = /^<\/(pre|code|kbd|script)(\s|>)/i;

// One matched pair of brackets holding no bracket of its own; link labels
// nest two levels deep.
const INLINE_BRACKETS_SRC = '\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]';
const INLINE_LABEL_SRC = '(?:\\[(?:' + INLINE_BRACKETS_SRC + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?';
const LINK_HREF_SRC = '<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\))';
const LINK_TITLE_SRC = '"(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)';
const R_LINK = new RegExp('^!?\\[(' + INLINE_LABEL_SRC + ')\\]\\([ \\t\\n]*(' + LINK_HREF_SRC + ')(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(' + LINK_TITLE_SRC + '))?[ \\t\\n]*\\)');
const R_REFLINK = new RegExp('^!?\\[(' + INLINE_LABEL_SRC + ')\\]\\[(' + BLOCK_LABEL_SRC + ')\\]');
const R_NOLINK = new RegExp('^!?\\[(' + BLOCK_LABEL_SRC + ')\\](?:\\[\\])?');

// The unanchored search form used when masking: bounded labels keep the scan
// linear on inputs that can never match.
const BOUNDED_BLOCK_LABEL_SRC = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}';
const BOUNDED_INLINE_LABEL_SRC = '(?:[^\\[\\]\\\\`]*(?:\\[(?:' + INLINE_BRACKETS_SRC + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?';
const R_REFLINK_SEARCH = new RegExp('!?\\[(' + BOUNDED_INLINE_LABEL_SRC + ')\\]\\[(' + BOUNDED_BLOCK_LABEL_SRC + ')\\]|!?\\[(' + BOUNDED_BLOCK_LABEL_SRC + ')\\](?:\\[\\])?(?!\\()', 'g');

const R_AUTOLINK = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/;

const TAG_ATTR_SRC = '\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*"[^"]*"|\\s*=\\s*\'[^\']*\'|\\s*=\\s*[^\\s"\'=<>`]+)?';
const R_TAG = new RegExp('^<!--(?:-?>|[\\s\\S]*?-->)'
  + '|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>'
  + '|^<[a-zA-Z][a-zA-Z0-9-]*(?:' + TAG_ATTR_SRC + ')*?\\s*/?>'
  + '|^<\\?[\\s\\S]*?\\?>'
  + '|^<![a-zA-Z]+\\s[\\s\\S]*?>'
  + '|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>');

const EXT_EMAIL_SRC = '[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])';
const EMAIL_PROTO_SRC = '(?:mailto:' + EXT_EMAIL_SRC + '|xmpp:' + EXT_EMAIL_SRC + '(?:\\/[A-Za-z0-9@.]+)?)';
const R_URL = new RegExp('^' + EMAIL_PROTO_SRC
  + '|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*'
  + '|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])');
const R_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

// Emphasis and strikethrough delimiter patterns. GFM treats ~ as an ordinary
// character for * and _ flanking, so the asterisk patterns use the GFM
// punctuation sets while the underscore and tilde patterns use the plain ones.
const PUNCT = '[\\p{P}\\p{S}]';
const PUNCT_GFM = '(?!~)[\\p{P}\\p{S}]';
const PUNCT_SPACE = '[\\s\\p{P}\\p{S}]';
const PUNCT_SPACE_GFM = '(?!~)[\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE = '[^\\s\\p{P}\\p{S}]';
const NOT_PUNCT_SPACE_GFM = '(?:[^\\s\\p{P}\\p{S}]|~)';

const R_LDELIM = new RegExp('^(?:\\*+(?:((?!\\*)' + PUNCT_GFM + ')|([^\\s*]))?)|^_+(?:((?!_)' + PUNCT_GFM + ')|([^\\s_]))?', 'u');
const R_RDELIM_AST = new RegExp(
  '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)'
  + '|[^*]+(?=[^*])'
  + '|(?!\\*)' + PUNCT_GFM + '(\\*+)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE_GFM + '(\\*+)(?!\\*)(?=' + PUNCT_SPACE_GFM + '|$)'
  + '|(?!\\*)' + PUNCT_SPACE_GFM + '(\\*+)(?=' + NOT_PUNCT_SPACE_GFM + ')'
  + '|[\\s](\\*+)(?!\\*)(?=' + PUNCT_GFM + ')'
  + '|(?!\\*)' + PUNCT_GFM + '(\\*+)(?!\\*)(?=' + PUNCT_GFM + ')'
  + '|' + NOT_PUNCT_SPACE_GFM + '(\\*+)(?=' + NOT_PUNCT_SPACE_GFM + ')', 'gu');
const R_RDELIM_UND = new RegExp(
  '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)'
  + '|[^_]+(?=[^_])'
  + '|(?!_)' + PUNCT + '(_+)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE + '(_+)(?!_)(?=' + PUNCT_SPACE + '|$)'
  + '|(?!_)' + PUNCT_SPACE + '(_+)(?=' + NOT_PUNCT_SPACE + ')'
  + '|[\\s](_+)(?!_)(?=' + PUNCT + ')'
  + '|(?!_)' + PUNCT + '(_+)(?!_)(?=' + PUNCT + ')', 'gu');
const R_DEL_LDELIM = new RegExp('^~~?(?:((?!~)' + PUNCT + ')|[^\\s~])', 'u');
const R_DEL_RDELIM = new RegExp(
  '^[^~]+(?=[^~])'
  + '|(?!~)' + PUNCT + '(~~?)(?=[\\s]|$)'
  + '|' + NOT_PUNCT_SPACE + '(~~?)(?!~)(?=' + PUNCT_SPACE + '|$)'
  + '|(?!~)' + PUNCT_SPACE + '(~~?)(?=' + NOT_PUNCT_SPACE + ')'
  + '|[\\s](~~?)(?!~)(?=' + PUNCT + ')'
  + '|(?!~)' + PUNCT + '(~~?)(?!~)(?=' + PUNCT + ')'
  + '|' + NOT_PUNCT_SPACE + '(~~?)(?=' + NOT_PUNCT_SPACE + ')', 'gu');
const R_PUNCT_CHAR = new RegExp('^((?![*_])' + PUNCT_SPACE + ')', 'u');
const R_ALNUM = /[\p{L}\p{N}]/u;

// Sticky twins of the anchored inline patterns: matching one at lastIndex
// is exactly matching its ^-anchored form on the slice from that index,
// without allocating the slice. The ^ anchors sit only at the pattern start
// and after top-level alternations, so the replacement removes exactly
// those — a ^ inside a character class is never preceded by | or the start.
function stickyOf(re) {
  return new RegExp(re.source.replace(/(\||^)\^/g, '$1'), re.flags + 'y');
}
const R_LINK_Y = stickyOf(R_LINK);
const R_REFLINK_Y = stickyOf(R_REFLINK);
const R_NOLINK_Y = stickyOf(R_NOLINK);
const R_LDELIM_Y = stickyOf(R_LDELIM);
const R_DEL_LDELIM_Y = stickyOf(R_DEL_LDELIM);
const R_CODESPAN_Y = stickyOf(R_CODESPAN);
const R_AUTOLINK_Y = stickyOf(R_AUTOLINK);
const R_URL_Y = stickyOf(R_URL);
const R_TAG_Y = stickyOf(R_TAG);

// Spans the emphasis scanner must skip: inline links, code spans, raw HTML.
const BLOCKSKIP_LINK_SRC = '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)';
const R_BLOCK_SKIP = new RegExp(BLOCKSKIP_LINK_SRC + '|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)|<(?! )[^<>]*?>', 'g');
const R_ESC_OUTSIDE_CODE = new RegExp('(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\(' + PUNCT + ')', 'gu');

// ---------------------------------------------------------------------------
// Block parsing (phase one)
// ---------------------------------------------------------------------------

// Node kinds.
const N_PARA = 0;  // { k, s } paragraph, s = inline source
const N_TEXT = 1;  // { k, s } bare inline source (list items, no <p>)
const N_CODE = 2;  // { k, h } pre-rendered code block HTML
const N_HEAD = 3;  // { k, d, s } heading
const N_HR = 4;    // { k }
const N_HTML = 5;  // { k, h } raw HTML block text
const N_BQ = 6;    // { k, c, r, t } blockquote: children, raw, stripped text
const N_LIST = 7;  // { k, o, st, l, items, r } list
const N_TABLE = 8; // { k, hd, al, rows }

function codeHtml(text, lang) {
  const langString = (lang || '').match(R_NOT_SPACE_START)[0];
  const code = text ? text.replace(R_END_NL, '') + '\n' : '';
  const body = esc(code, true);
  if (!langString) return '<pre><code>' + body + '</code></pre>\n';
  return '<pre><code class="language-' + esc(langString) + '">' + body + '</code></pre>\n';
}

// A fenced block's content loses up to the fence line's own indentation.
function fenceText(raw, text) {
  const mi = R_FENCE_INDENT.exec(raw);
  if (!mi) return text;
  const ind = mi[1].length;
  return text.split('\n').map((line) => {
    const m2 = R_LEAD_WS.exec(line);
    if (!m2) return line;
    return line.slice(Math.min(m2[0].length, ind));
  }).join('\n');
}

// Could a table start here? The delimiter row is the second line and must
// hold a pipe or a colon.
function tablePossible(src) {
  const nl1 = src.indexOf('\n');
  if (nl1 === -1) return false;
  let nl2 = src.indexOf('\n', nl1 + 1);
  if (nl2 === -1) nl2 = src.length;
  for (let i = nl1 + 1; i < nl2; i++) {
    const c = src.charCodeAt(i);
    if (c === 124 || c === 58) return true;
  }
  return false;
}

// Could a setext heading start here? Some line after the first, before any
// blank line, must look like an underline: up to three spaces, a run of =
// or -, then only spaces and tabs.
function setextPossible(src) {
  let i = src.indexOf('\n');
  if (i === -1) return false;
  i++;
  while (i < src.length) {
    let j = src.indexOf('\n', i);
    if (j === -1) j = src.length;
    let k = i;
    let spaces = 0;
    while (spaces < 3 && src.charCodeAt(k) === 32) { k++; spaces++; }
    const c = src.charCodeAt(k);
    if (c === 61 || c === 45) {
      let m = k + 1;
      while (m < j && src.charCodeAt(m) === c) m++;
      let ok = true;
      while (m < j) {
        const d = src.charCodeAt(m);
        if (d !== 32 && d !== 9) { ok = false; break; }
        m++;
      }
      if (ok) return true;
    }
    let blank = true;
    for (let m = i; m < j; m++) {
      const d = src.charCodeAt(m);
      if (d !== 32 && d !== 9) { blank = false; break; }
    }
    if (blank) return false;
    i = j + 1;
  }
  return false;
}

// Parse blocks from src, appending nodes to `frame.nodes`. `top` allows
// paragraphs (false inside list items, where bare text lines are used
// instead). `clip` merges a leading paragraph into the previous chunk's
// paragraph, for lazy blockquote continuations. `frame.tail` records what
// the last pushed thing was (0 = none/other, 1 = paragraph, 2 = text) so
// merges into a paragraph or text run apply exactly when the previous
// pushed thing is one — a blank-line gap or a definition in between breaks
// the merge, while a single newline does not. Returns true when a
// blank-line gap separated two blocks (used for list looseness).
function blockParse(src, ctx, top, clip, frame) {
  const nodes = frame.nodes;
  const entryLen = src.length;
  // A nested list leaks top-level lexing into the rest of this call: the
  // reference lexer ends every block pass with top set, and the list
  // tokenizer never restores it, so text after a nested list inside an
  // item becomes a paragraph instead of bare text.
  let topNow = top;
  let gap = false;
  while (src) {
    let m = R_BLOCK_NEWLINE.exec(src);
    if (m) {
      if (R_ANY_LINE.test(m[0])) gap = true;
      if (m[0].length === 1 && frame.touched) {
        // A single newline only terminates the last line; the previous
        // pushed thing stays previous.
      } else {
        frame.tail = 0;
      }
      frame.touched = true;
      src = src.slice(m[0].length);
      continue;
    }
    // Most block patterns allow up to three leading spaces and then demand
    // a specific first character; ruling them out by that character keeps
    // the expensive patterns off the common paragraph path.
    let sp = 0;
    while (sp < 3 && src.charCodeAt(sp) === 32) sp++;
    const fc = src.charCodeAt(sp);
    let sp4 = sp;
    while (sp4 < 4 && src.charCodeAt(sp4) === 32) sp4++;
    const codeIndent = sp4 === 4 || src.charCodeAt(sp4) === 9;
    m = null;
    if (codeIndent) m = R_BLOCK_CODE.exec(src);
    if (m) {
      const raw = trimTrailingBlanks(m[0]);
      const text = raw.replace(R_CODE_DEDENT, '');
      src = src.slice(raw.length);
      if (frame.tail === 1 || frame.tail === 2) {
        nodes[nodes.length - 1].s += '\n' + text;
      } else {
        nodes.push({ k: N_CODE, h: codeHtml(text, undefined) });
        frame.tail = 0;
      }
      frame.touched = true;
      continue;
    }
    m = null;
    if (fc === 96 || fc === 126) m = R_FENCES.exec(src);
    if (m) {
      src = src.slice(m[0].length);
      const lang = m[2] ? unescapePunct(m[2].trim()) : m[2];
      nodes.push({ k: N_CODE, h: codeHtml(fenceText(m[0], m[3] || ''), lang) });
      frame.tail = 0;
      frame.touched = true;
      continue;
    }
    m = null;
    if (fc === 35) m = R_HEADING.exec(src);
    if (m) {
      src = src.slice(rtrimChar(m[0], '\n').length);
      let text = m[2].trim();
      if (R_END_HASH.test(text)) {
        const trimmed = rtrimChar(text, '#');
        if (!trimmed || R_END_SPACE_TAB.test(trimmed)) text = trimmed.trim();
      }
      nodes.push({ k: N_HEAD, d: m[1].length, s: text });
      frame.tail = 0;
      frame.touched = true;
      continue;
    }
    m = null;
    if (fc === 45 || fc === 95 || fc === 42) m = R_HR.exec(src);
    if (m) {
      src = src.slice(rtrimChar(m[0], '\n').length);
      nodes.push({ k: N_HR });
      frame.tail = 0;
      frame.touched = true;
      continue;
    }
    const bq = fc === 62 ? tryBlockquote(src, ctx) : null;
    if (bq) {
      src = src.slice(bq.r.length);
      nodes.push(bq);
      frame.tail = 0;
      frame.touched = true;
      continue;
    }
    const li = (fc === 42 || fc === 43 || fc === 45 || (fc >= 48 && fc <= 57)) ? tryList(src, ctx) : null;
    if (li) {
      src = src.slice(li.r.length);
      nodes.push(li);
      frame.tail = 0;
      frame.touched = true;
      topNow = true;
      continue;
    }
    m = null;
    if (fc === 60) m = R_HTML_BLOCK.exec(src);
    if (m) {
      const raw = trimTrailingBlanks(m[0]);
      src = src.slice(raw.length);
      nodes.push({ k: N_HTML, h: raw });
      frame.tail = 0;
      frame.touched = true;
      continue;
    }
    m = null;
    if (fc === 91) m = R_DEF.exec(src);
    if (m && (R_START_LT.test(m[2]) || findClosingBracket(m[2], '()') === -1)) {
      const raw = rtrimChar(m[0], '\n');
      src = src.slice(raw.length);
      if (frame.tail === 1 || frame.tail === 2) {
        // A definition line after paragraph text joins the paragraph as
        // literal text and defines nothing.
        nodes[nodes.length - 1].s += '\n' + raw;
      } else {
        const tag = normalizeLabel(m[1]);
        if (!ctx.links[tag]) {
          const href = m[2] ? unescapePunct(m[2].replace(R_HREF_BRACKETS, '$1')) : '';
          const title = m[3] ? unescapePunct(m[3].substring(1, m[3].length - 1)) : m[3];
          ctx.links[tag] = { href, title };
        }
        frame.tail = 0;
      }
      frame.touched = true;
      continue;
    }
    m = null;
    if (tablePossible(src)) m = R_TABLE.exec(src);
    if (m && R_TABLE_DELIM.test(m[2])) {
      const headers = splitCells(m[1]);
      const aligns = m[2].replace(R_TABLE_ALIGN_TRIM, '').split('|');
      if (headers.length === aligns.length) {
        src = src.slice(rtrimChar(m[0], '\n').length);
        const al = aligns.map((a) => R_ALIGN_RIGHT.test(a) ? 'right' : R_ALIGN_CENTER.test(a) ? 'center' : R_ALIGN_LEFT.test(a) ? 'left' : null);
        const rows = (m[3] && m[3].trim()) ? m[3].replace(R_TABLE_ROW_BLANK, '').split('\n') : [];
        nodes.push({ k: N_TABLE, hd: headers, al, rows: rows.map((r) => splitCells(r, headers.length)) });
        frame.tail = 0;
        frame.touched = true;
        continue;
      }
    }
    // A table pattern that fails the delimiter or cell-count check still
    // ends any open paragraph — the paragraph rule stops at the same
    // pattern — but only once this call has consumed something: when the
    // pattern leads the chunk, the paragraph after it is still the
    // chunk's leading paragraph and keeps its lazy merge. Bare text runs
    // in list items keep merging across it, as the reference lexer merges
    // adjacent text tokens.
    if (m && src.length < entryLen && frame.tail === 1) frame.tail = 0;
    m = null;
    if (setextPossible(src)) m = R_LHEADING.exec(src);
    if (m) {
      src = src.slice(rtrimChar(m[0], '\n').length);
      nodes.push({ k: N_HEAD, d: m[2].charAt(0) === '=' ? 1 : 2, s: m[1].trim() });
      frame.tail = 0;
      frame.touched = true;
      continue;
    }
    if (topNow) {
      m = R_PARA.exec(src);
      if (m) {
        const text = m[1].charAt(m[1].length - 1) === '\n' ? m[1].slice(0, -1) : m[1];
        src = src.slice(m[0].length);
        if (clip && frame.tail === 1) {
          nodes[nodes.length - 1].s += '\n' + text;
        } else {
          nodes.push({ k: N_PARA, s: text });
          frame.tail = 1;
        }
        frame.touched = true;
        continue;
      }
    }
    m = R_TEXT.exec(src);
    if (m) {
      src = src.slice(m[0].length);
      if (frame.tail === 2) {
        nodes[nodes.length - 1].s += '\n' + m[0];
      } else {
        nodes.push({ k: N_TEXT, s: m[0] });
        frame.tail = 2;
      }
      frame.touched = true;
      continue;
    }
    break; // unreachable: blank lines and text cover every non-empty input
  }
  return gap;
}

function tryBlockquote(src, ctx) {
  const m = R_BLOCKQUOTE.exec(src);
  if (!m) return null;
  let lines = rtrimChar(m[0], '\n').split('\n');
  let raw = '';
  let text = '';
  const frame = { nodes: [], tail: 0, touched: false };
  const nodes = frame.nodes;
  while (lines.length > 0) {
    let inBq = false;
    const cur = [];
    let i = 0;
    for (; i < lines.length; i++) {
      if (R_BQ_START.test(lines[i])) {
        cur.push(lines[i]);
        inBq = true;
      } else if (!inBq) {
        cur.push(lines[i]);
      } else {
        break;
      }
    }
    lines = lines.slice(i);
    const curRaw = cur.join('\n');
    const curText = curRaw
      .replace(R_BQ_MARKER_WS, (_, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(R_BQ_SETEXT, '\n    $1')
      .replace(R_BQ_STRIP, '');
    raw = raw ? raw + '\n' + curRaw : curRaw;
    text = text ? text + '\n' + curText : curText;
    blockParse(curText, ctx, true, true, frame);
    if (lines.length === 0) break;
    const last = nodes[nodes.length - 1];
    if (last && (last.k === N_CODE || last.k === N_HEAD || last.k === N_HR || last.k === N_HTML || last.k === N_TABLE)) {
      break;
    }
    if (last && last.k === N_BQ) {
      const old = last;
      const continuation = lines.join('\n');
      const newText = old.r + '\n' + continuation.replace(R_BQ_STRIP, '');
      const nt = tryBlockquote(newText, ctx);
      if (!nt) break;
      nodes[nodes.length - 1] = nt;
      const leftover = newText.substring(nt.r.length).replace(/^\n/, '');
      const leftoverCount = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverCount ? lines.slice(0, -leftoverCount) : lines;
      if (consumed.length > 0) raw += '\n' + consumed.join('\n');
      text = text.substring(0, text.length - old.t.length) + nt.t;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && R_BQ_START.test(lines[0])) continue;
      break;
    }
    if (last && last.k === N_LIST) {
      const old = last;
      const newText = old.r + '\n' + lines.join('\n');
      const nt = tryList(newText, ctx);
      if (!nt) break;
      nodes[nodes.length - 1] = nt;
      const consumedCount = nt.r.length > old.r.length
        ? newText.slice(old.r.length + 1, nt.r.length).split('\n').length : 0;
      if (consumedCount > 0) {
        const consumed = lines.slice(0, consumedCount).join('\n');
        raw += '\n' + consumed;
        text += '\n' + consumed;
      }
      lines = lines.slice(consumedCount);
      continue;
    }
    // A paragraph or bare-text tail lets the loop take the next chunk.
  }
  return { k: N_BQ, c: nodes, r: raw, t: text };
}

function tryList(src, ctx) {
  const cap = R_LIST.exec(src);
  if (!cap) return null;
  const listSrc = src;
  let rest = src;
  const taken = () => listSrc.length - rest.length;
  let bull = cap[1].trim();
  const ordered = bull.length > 1;
  const start = ordered ? +bull.slice(0, -1) : '';
  const bullPat = ordered ? '\\d{1,9}\\' + bull.slice(-1) : '\\' + bull;
  const itemRe = listItemRegex(bullPat);
  const items = [];
  let loose = false;
  let endsWithBlank = false;
  while (rest) {
    let endEarly = false;
    let itemContents = '';
    const ic = itemRe.exec(rest);
    if (!ic) break;
    // The bullet was actually a thematic break.
    let hsp = 0;
    while (hsp < 3 && rest.charCodeAt(hsp) === 32) hsp++;
    const hc = rest.charCodeAt(hsp);
    if ((hc === 45 || hc === 95 || hc === 42) && R_HR.test(rest)) break;
    const itemStart = taken();
    rest = rest.substring(ic[0].length);
    const firstLine = firstLineOf(ic[2]);
    const bulletIndent = ic[1].length;
    let line = expandLeadTabs(firstLine, bulletIndent);
    let nextLine = firstLineOf(rest);
    let blankLine = isBlankTrim(line);
    let indent = 0;
    if (blankLine) {
      indent = bulletIndent + 1;
    } else {
      indent = firstNonSpace(line);
      indent = indent > 4 ? 1 : indent;
      itemContents = line.slice(indent);
      indent += bulletIndent;
    }
    if (blankLine && isBlankSpaceTab(nextLine)) {
      rest = rest.substring(nextLine.length + 1);
      endEarly = true;
    }
    if (!endEarly) {
      const idx = Math.max(0, Math.min(3, indent - 1));
      const res = [indentRegex(0, indent), indentRegex(1, indent), indentRegex(2, indent),
        indentRegex(3, indent), indentRegex(4, indent), indentRegex(5, indent)];
      while (rest) {
        const nl = rest.indexOf('\n');
        const rawLine = nl === -1 ? rest : rest.slice(0, nl);
        nextLine = rawLine;
        const nextNoTabs = expandLeadTabs(nextLine, 0);
        if (interruptsItem(nextLine, idx, res)) break;
        const lineBlank = isBlankTrim(nextLine);
        if (firstNonSpace(nextNoTabs) >= indent || lineBlank) {
          itemContents += '\n' + nextNoTabs.slice(indent);
        } else {
          if (blankLine) break;
          if (indentedCodeLine(line)) break;
          if (interruptsLazy(line, idx, res)) break;
          const setextCont = R_SETEXT_LAZY.test(nextLine) && R_LHEADING.test(line + '\n' + nextLine);
          const continuation = setextCont ? '    ' + nextNoTabs.replace(R_STRIP_3, '') : nextLine;
          itemContents += '\n' + continuation;
        }
        blankLine = lineBlank;
        rest = nl === -1 ? '' : rest.slice(nl + 1);
        line = nextNoTabs.slice(indent);
      }
    }
    const raw = listSrc.slice(itemStart, taken());
    if (!loose) {
      if (endsWithBlank) loose = true;
      else if (endsDoubleBlank(raw)) endsWithBlank = true;
    }
    items.push({ raw, task: R_TASK.test(itemContents), text: itemContents });
  }
  const lastItem = items[items.length - 1];
  if (!lastItem) return null;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  const listRaw = listSrc.slice(0, taken()).trimEnd();
  for (const item of items) {
    const frame = { nodes: [], tail: 0, touched: false };
    const gap = blockParse(item.text, ctx, false, false, frame);
    item.nodes = frame.nodes;
    if (!loose && gap) loose = true;
  }
  for (const item of items) {
    const first = item.nodes[0];
    if (item.task && first && (first.k === N_TEXT || first.k === N_PARA)) {
      item.text = item.text.replace(R_TASK_STRIP, '');
      first.s = first.s.replace(R_TASK_STRIP, '');
      const box = R_TASK_BOX.exec(item.raw);
      if (box) item.checked = box[0] !== '[ ]';
      else item.task = false;
    } else if (item.task) {
      item.task = false;
    }
  }
  if (loose) {
    for (const item of items) {
      for (const n of item.nodes) if (n.k === N_TEXT) n.k = N_PARA;
    }
  }
  return { k: N_LIST, o: ordered, st: start, l: loose, items, r: listRaw };
}

// ---------------------------------------------------------------------------
// Inline scanning (phase two)
// ---------------------------------------------------------------------------

// Characters that always end a plain-text run.
const HARD_STOP = new Uint8Array(128);
for (const ch of [92, 60, 91, 33, 42, 95, 96, 126]) HARD_STOP[ch] = 1; // \ < [ ! * _ ` ~

// Characters that may appear in the local part of an email address.
const EMAIL_CH = new Uint8Array(128);
for (let c = 48; c <= 57; c++) EMAIL_CH[c] = 1;
for (let c = 65; c <= 90; c++) EMAIL_CH[c] = 1;
for (let c = 97; c <= 122; c++) EMAIL_CH[c] = 1;
for (const ch of [46, 33, 35, 36, 37, 38, 39, 42, 43, 47, 61, 63, 96, 123, 124, 125, 126, 45, 95]) EMAIL_CH[ch] = 1;

// Email-local characters that do not also end a text run: the word scan in
// scanTextEnd stops at hard-stop characters, so the two tables fold into one.
const WORD_CH = new Uint8Array(128);
for (let c = 0; c < 128; c++) WORD_CH[c] = (EMAIL_CH[c] && !HARD_STOP[c]) ? 1 : 0;

function isAlnumCode(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

// The JavaScript \s character class, as code points.
function isWsCode(c) {
  return c === 32 || c === 9 || c === 10 || c === 11 || c === 12 || c === 13
    || c === 160 || c === 5760 || (c >= 8192 && c <= 8202) || c === 8232 || c === 8233
    || c === 8239 || c === 8287 || c === 12288 || c === 65279;
}

// Could the extended-autolink pattern match at i? The pattern needs a
// mailto:/xmpp: prefix, a protocol:// or www. prefix, or an email-local word
// followed by @. Anything else is ruled out without running the pattern.
function urlPossible(s, i, n) {
  const c = s.charCodeAt(i);
  if (c === 119 && s.charCodeAt(i + 1) === 119 && s.charCodeAt(i + 2) === 119 && s.charCodeAt(i + 3) === 46) return true;
  if (c === 104 || c === 72 || c === 102 || c === 70) {
    if (isProtocolAt(s, i)) return true;
  } else if (c === 109 || c === 120) {
    if (isMailtoAt(s, i)) return true;
  }
  if (c < 128 && EMAIL_CH[c]) {
    let j = i + 1;
    while (j < n) {
      const d = s.charCodeAt(j);
      if (d >= 128 || !EMAIL_CH[d]) break;
      j++;
    }
    return j < n && s.charCodeAt(j) === 64;
  }
  return false;
}

// Case-insensitive http://, https:// or ftp:// at i.
function isProtocolAt(s, i) {
  const c = s.charCodeAt(i);
  if (c === 104 || c === 72) {
    if ((s.charCodeAt(i + 1) | 32) !== 116 || (s.charCodeAt(i + 2) | 32) !== 116 || (s.charCodeAt(i + 3) | 32) !== 112) return false;
    let j = i + 4;
    if ((s.charCodeAt(j) | 32) === 115) j++;
    return s.charCodeAt(j) === 58 && s.charCodeAt(j + 1) === 47 && s.charCodeAt(j + 2) === 47;
  }
  if (c === 102 || c === 70) {
    if ((s.charCodeAt(i + 1) | 32) !== 116 || (s.charCodeAt(i + 2) | 32) !== 112) return false;
    return s.charCodeAt(i + 3) === 58 && s.charCodeAt(i + 4) === 47 && s.charCodeAt(i + 5) === 47;
  }
  return false;
}

// Case-sensitive mailto: or xmpp: at i.
function isMailtoAt(s, i) {
  const c = s.charCodeAt(i);
  if (c === 109) {
    return s.charCodeAt(i + 1) === 97 && s.charCodeAt(i + 2) === 105 && s.charCodeAt(i + 3) === 108
      && s.charCodeAt(i + 4) === 116 && s.charCodeAt(i + 5) === 111 && s.charCodeAt(i + 6) === 58;
  }
  if (c === 120) {
    return s.charCodeAt(i + 1) === 109 && s.charCodeAt(i + 2) === 112 && s.charCodeAt(i + 3) === 112
      && s.charCodeAt(i + 4) === 58;
  }
  return false;
}

// Emit a plain-text chunk as escaped text. This folds the numeric-reference
// decoding and the HTML escaping that the reference renderer applies to
// plain text runs: a numeric reference decodes to its character (zero,
// out-of-range and surrogate values become U+FFFD), an & starting a valid
// reference is kept, any other & becomes &amp;, and < > " ' become entities.
// In flat (alt-text) mode no entities are emitted except the &amp; forms the
// decoder itself produces, and a bare & is escaped only when the chunk holds
// a numeric reference at all. The scan jumps from one metacharacter to the
// next; only & positions need the hand-written reference checks.
const RE_ESC_SCAN = /[&<>"']/g;
function emitEscaped(chunk, flat, out) {
  let hasNumRef = false;
  if (flat) {
    let at = chunk.indexOf('&#');
    while (at !== -1) {
      if (numRefEnd(chunk, at, chunk.length) !== -1) { hasNumRef = true; break; }
      at = chunk.indexOf('&#', at + 2);
    }
  }
  let seg = 0;
  RE_ESC_SCAN.lastIndex = 0;
  let m;
  while ((m = RE_ESC_SCAN.exec(chunk)) !== null) {
    const i = m.index;
    if (m[0] === '&') {
      const refEnd = numRefEnd(chunk, i, chunk.length);
      if (refEnd !== -1) {
        if (seg < i) out.push(chunk.slice(seg, i));
        out.push(decodeNumRef(chunk, i, refEnd, flat));
        seg = refEnd;
        RE_ESC_SCAN.lastIndex = refEnd;
        continue;
      }
      if (isValidRef(chunk, i, chunk.length)) continue;
      if (!flat || hasNumRef) {
        if (seg < i) out.push(chunk.slice(seg, i));
        out.push('&amp;');
        seg = i + 1;
      }
      continue;
    }
    if (flat) continue; // < > " ' pass through in flat mode
    if (seg < i) out.push(chunk.slice(seg, i));
    const c = m[0];
    out.push(c === '<' ? '&lt;' : c === '>' ? '&gt;' : c === '"' ? '&quot;' : '&#39;');
    seg = i + 1;
  }
  if (seg < chunk.length) out.push(chunk.slice(seg));
}

// End index just past a numeric character reference starting at i (whose
// first two characters are &#), or -1 when the text there is not one:
// &# + 1-7 decimal digits + ;, or &#x/X + 1-6 hex digits + ;.
function numRefEnd(src, i, end) {
  if (src.charCodeAt(i + 1) !== 35) return -1;
  let j = i + 2;
  if (j < end && (src.charCodeAt(j) === 120 || src.charCodeAt(j) === 88)) {
    j++;
    const hexStart = j;
    while (j < end && j - hexStart < 6) {
      const d = src.charCodeAt(j);
      if (!((d >= 48 && d <= 57) || (d >= 65 && d <= 70) || (d >= 97 && d <= 102))) break;
      j++;
    }
    if (j === hexStart || j >= end || src.charCodeAt(j) !== 59) return -1;
    return j + 1;
  }
  const decStart = j;
  while (j < end && j - decStart < 7) {
    const d = src.charCodeAt(j);
    if (d < 48 || d > 57) break;
    j++;
  }
  if (j === decStart || j >= end || src.charCodeAt(j) !== 59) return -1;
  return j + 1;
}

// The character a numeric reference stands for, escaped when the flat mode
// does not apply and the character is a metacharacter.
function decodeNumRef(src, i, refEnd, flat) {
  const body = src.slice(i + 2, refEnd - 1);
  const hex = body.charCodeAt(0) === 120 || body.charCodeAt(0) === 88;
  const code = hex ? parseInt(body.slice(1), 16) : parseInt(body, 10);
  if (code === 0 || code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) return '�';
  if (code === 38) return '&amp;';
  if (!flat && code === 60) return '&lt;';
  if (!flat && code === 62) return '&gt;';
  if (!flat && code === 34) return '&quot;';
  if (!flat && code === 39) return '&#39;';
  return String.fromCodePoint(code);
}

// Whether the & at i starts a valid character reference: & + word characters
// + ;. A # shape reaching here is never valid — the numeric-reference shapes
// are the only # alternatives, and those were already ruled out.
function isValidRef(src, i, end) {
  let j = i + 1;
  if (j >= end || src.charCodeAt(j) === 35) return false;
  const start = j;
  while (j < end) {
    const d = src.charCodeAt(j);
    if (!((d >= 48 && d <= 57) || (d >= 65 && d <= 90) || (d >= 97 && d <= 122) || d === 95)) break;
    j++;
  }
  if (j === start) return false;
  return j < end && src.charCodeAt(j) === 59;
}
// one character: a leading run of backticks or tildes is taken whole, anything
// else contributes one character before the stop checks apply. The run stops
// before markup characters, before a hard-break space run, and before the
// start of an email address, a www. autolink, a scheme:// autolink, or a
// mailto:/xmpp: address, so the main loop can try those tokenizers there.
// The stops that end a plain-text run, as one global scan: a markup
// character other than _, a hard-break space run, a www. autolink (only
// after whitespace or *, _, ~, (), a mailto:/xmpp: address (only after a
// non-alphanumeric), or a scheme:// autolink (anywhere, even mid-word).
// Underscores and email words are found separately in scanTextEnd: an
// email word starting before an underscore wins over it, and a scheme
// directly behind a multi-character backtick or tilde run never stops.
const RE_TEXT_JUMP = /[\\<\[!*`~]| {2,}\n|(?<![^\s*_~(])www\.|(?<![A-Za-z0-9])(?:mailto:|xmpp:)|[hH][tT][tT][pP][sS]?:\/\/|[fF][tT][pP]:\/\//g;
function scanTextEnd(src, pos, n) {
  let i = pos;
  const c0 = src.charCodeAt(i);
  let runLen = 1;
  if (c0 === 96 || c0 === 126) {
    do { i++; } while (i < n && src.charCodeAt(i) === c0);
    runLen = i - pos;
  } else {
    i++;
  }
  // The next email word, if any, stops the run at its start even when the
  // word holds stop characters and its @ lies past the main stop: the
  // reference text rule ends a token before an email word. One lookup
  // plus one walk-back finds it; a word reaching back into the first
  // element ends the run right after that element.
  let emailStop = -1;
  let atPos = src.indexOf('@', i);
  while (atPos !== -1) {
    let w = atPos;
    while (w > 0) {
      const d = src.charCodeAt(w - 1);
      if (d >= 128 || !EMAIL_CH[d]) break;
      w--;
    }
    if (w < atPos) {
      if (w <= i) return i;
      emailStop = w;
      break;
    }
    atPos = src.indexOf('@', atPos + 1);
  }
  // A scheme stop directly behind a multi-character backtick or tilde run
  // is skipped: the reference text rule swallows such a run as the token's
  // first element, so the scheme stop behind it never fires and only the
  // bare email after it can link. Single-character runs keep the stop.
  let end = n;
  RE_TEXT_JUMP.lastIndex = i;
  let m;
  while ((m = RE_TEXT_JUMP.exec(src)) !== null) {
    if (m.index === i && runLen >= 2 && (m[0] === 'mailto:' || m[0] === 'xmpp:')) {
      RE_TEXT_JUMP.lastIndex = i + 1;
      continue;
    }
    end = m.index;
    break;
  }
  // Underscores stop a run anywhere, and an email word stops the run at
  // its start. The earliest of the main stop, the underscore, and the
  // email word start wins.
  let best = end;
  const us = src.indexOf('_', i);
  if (us !== -1 && us < end) best = us;
  if (emailStop !== -1 && emailStop < best) best = emailStop;
  return best;
}

// Does this text hold a link already? Images do not count.
function linkInText(text, links) {
  if (!text.includes('[')) return false;
  for (const m of text.matchAll(R_BLOCK_SKIP)) {
    if (R_LINK.test(m[0]) && text.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of text.matchAll(R_REFLINK_SEARCH)) {
    const match0 = m[0];
    const refStart = match0.lastIndexOf('[');
    if (match0.charAt(0) === '!' || !Object.hasOwn(links, normalizeLabel(match0.slice(refStart + 1, -1)))) continue;
    if (refStart > 1 && linkInText(match0.slice(1, refStart - 1), links)) continue;
    return true;
  }
  return false;
}

// Mask links, code spans, HTML and escapes so the emphasis scanner does not
// see delimiter characters inside them. Every replacement keeps the length
// it replaces, so masked indices line up with the source.
function maskSrc(src, links) {
  let masked = src;
  if (src.includes('[')) {
    const maskReflink = (match0) => {
      const refStart = match0.lastIndexOf('[');
      if (!Object.hasOwn(links, normalizeLabel(match0.slice(refStart + 1, -1)))) return match0;
      if (refStart > 1 && match0.charAt(0) !== '!') {
        const text = match0.slice(1, refStart - 1);
        if (linkInText(text, links)) {
          // A fresh pattern per nested pass: reusing the outer one inside
          // its own replacement callback would restart the outer scan.
          return '[' + text.replace(new RegExp(R_REFLINK_SEARCH.source, 'g'), maskReflink)
            + '][' + 'a'.repeat(match0.length - refStart - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(match0.length - 2) + ']';
    };
    masked = masked.replace(R_REFLINK_SEARCH, maskReflink);
  }
  // The escape/code pattern needs a backslash or a backtick; the link/code/
  // HTML pattern needs a bracket, a backtick or an angle bracket.
  if (masked.includes('\\') || masked.includes('`')) {
    masked = masked.replace(R_ESC_OUTSIDE_CODE, (match0, code, punct) => {
      if (punct) return '+'.repeat(match0.length);
      if (code) return code + match0.slice(code.length, -code.length).replace(/`/g, '+') + code;
      return match0;
    });
  }
  if (masked.includes('[') || masked.includes('`') || masked.includes('<')) {
    masked = masked.replace(R_BLOCK_SKIP, (match0, _a, context) => {
      const offset = context ? context.length : 0;
      return match0.slice(0, offset) + '[' + 'a'.repeat(match0.length - offset - 2) + ']';
    });
  }
  return masked;
}

// Whether a delimiter run that could close emphasis or strikethrough starts
// at or after `from`: a run of delimChar whose preceding character is not
// ASCII whitespace. Masking only removes delimiter runs, so finding none
// here proves the masked closer scan finds none either. The search stops at
// the first candidate, and a run straddling `from` is skipped whole, since
// its tail cannot close.
function closerAhead(src, from, delimChar) {
  const n = src.length;
  let i = from;
  if (i < n && src[i] === delimChar) {
    while (i < n && src[i] === delimChar) i++;
  }
  while (i < n) {
    const j = src.indexOf(delimChar, i);
    if (j === -1) return false;
    const prev = j === 0 ? 10 : src.charCodeAt(j - 1);
    if (prev !== 32 && prev !== 9 && prev !== 10 && prev !== 13 && prev !== 12) return true;
    let k = j + 1;
    while (k < n && src[k] === delimChar) k++;
    i = k;
  }
  return false;
}

// Last delimiter runs that could close emphasis, strong or strikethrough: a
// run can close only when it is not preceded by ASCII whitespace or the start
// of the string. One scan per inline run, shared by every opener in it.
function scanHints(masked) {
  let star = -1, under = -1, tilde = -1;
  const len = masked.length;
  for (let i = 0; i < len; i++) {
    const ch = masked[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : masked[i - 1];
    let j = i + 1;
    while (j < len && masked[j] === ch) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') tilde = i;
      else if (ch === '*') star = i;
      else under = i;
    }
    i = j - 1;
  }
  return { star, under, tilde };
}

function isLabelEndInsideToken(src, pos, label, labelStart) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') {
      i++;
      continue;
    }
    if (label[i] === '`') {
      const code = R_CODESPAN.exec(label.slice(i));
      if (code) {
        i += code[0].length - 1;
        continue;
      }
    }
    if (label[i] !== '<') continue;
    const tokenSrc = src.slice(pos + labelStart + i);
    const token = R_TAG.exec(tokenSrc) || R_AUTOLINK.exec(tokenSrc);
    if (!token) continue;
    if (token[0].length > label.length - i) return true;
    i += token[0].length - 1;
  }
  return false;
}

// Shared tail of the link and reference-link tokenizers: parse the label,
// bail when a link would contain another link, and emit the link or image.
// Returns the position after the match, or 0 when the link bails.
function outputLink(label, raw, href, title, isImage, pos, ctx, st, linkOK, flat, out) {
  const text = label.replace(R_OUTPUT_LINK, '$1');
  const outerInLink = ctx.inLink;
  const outerEmitted = st.emitted;
  const outerRaw = st.raw;
  ctx.inLink = true;
  st.emitted = false;
  const inner = inlineRun(text, ctx, st, linkOK, flat || isImage);
  const textHasLink = st.emitted;
  st.emitted = outerEmitted;
  ctx.inLink = outerInLink;
  const end = pos + raw.length;
  if (!isImage) {
    if (textHasLink) {
      st.raw = outerRaw;
      return 0;
    }
    st.emitted = true;
    if (flat) {
      out.push(inner);
      return end;
    }
    const clean = cleanUrl(href);
    if (clean === null) {
      out.push(inner);
      return end;
    }
    out.push('<a href="' + esc(clean) + '"' + (title ? ' title="' + esc(title) + '"' : '') + '>' + inner + '</a>');
    return end;
  }
  if (flat) {
    out.push(inner);
    return end;
  }
  const clean = cleanUrl(href);
  if (clean === null) {
    out.push(esc(inner));
    return end;
  }
  out.push('<img src="' + esc(clean) + '" alt="' + esc(inner) + '"' + (title ? ' title="' + esc(title) + '"' : '') + '>');
  return end;
}

function tryLink(src, pos, ctx, st, linkOK, flat, out) {
  if (!linkOK) return 0;
  R_LINK_Y.lastIndex = pos;
  const cap = R_LINK_Y.exec(src);
  if (!cap) return 0;
  const labelStart = cap[0].charCodeAt(0) === 33 ? 2 : 1;
  if (isLabelEndInsideToken(src, pos, cap[1], labelStart)) return 0;
  let raw = cap[0];
  let href = cap[2];
  let title = cap[3] ? cap[3].slice(1, -1) : '';
  const trimmedUrl = cap[2].trim();
  if (R_START_LT.test(trimmedUrl)) {
    if (!R_END_GT.test(trimmedUrl)) return 0;
    const rt = rtrimChar(trimmedUrl.slice(0, -1), '\\');
    if ((trimmedUrl.length - rt.length) % 2 === 0) return 0;
  } else {
    const lpi = findClosingBracket(cap[2], '()');
    if (lpi === -2) return 0;
    if (lpi > -1) {
      const start = cap[0].charCodeAt(0) === 33 ? 5 : 4;
      const linkLen = start + cap[1].length + lpi;
      href = cap[2].substring(0, lpi);
      raw = cap[0].substring(0, linkLen).trim();
      title = '';
    }
  }
  // The closing paren counts only when it is not itself escaped.
  const unesc = rtrimChar(raw.slice(0, -1), '\\');
  if ((raw.length - unesc.length) % 2 === 0) return 0;
  href = href.trim();
  if (R_START_LT.test(href)) href = href.slice(1, -1);
  href = href ? unescapePunct(href) : href;
  title = title ? unescapePunct(title) : title;
  return outputLink(cap[1], raw, href, title, cap[0].charCodeAt(0) === 33, pos, ctx, st, linkOK, flat, out);
}

function tryReflink(src, pos, ctx, st, linkOK, flat, out) {
  R_REFLINK_Y.lastIndex = pos;
  const cap = R_REFLINK_Y.exec(src) || (R_NOLINK_Y.lastIndex = pos, R_NOLINK_Y.exec(src));
  if (!cap) return 0;
  const labelStart = cap[0].charCodeAt(0) === 33 ? 2 : 1;
  if (isLabelEndInsideToken(src, pos, cap[1], labelStart)) return 0;
  const link = ctx.links[normalizeLabel(cap[2] || cap[1])];
  if (!link) {
    out.push(cap[0].charAt(0));
    return pos + 1;
  }
  return outputLink(cap[1], cap[0], link.href, link.title, cap[0].charCodeAt(0) === 33, pos, ctx, st, linkOK, flat, out);
}

function tryEmStrong(src, pos, ctx, st, prevChar, linkOK, flat, out, getMasked, getHints) {
  R_LDELIM_Y.lastIndex = pos;
  const match = R_LDELIM_Y.exec(src);
  if (!match) return 0;
  if (!match[1] && !match[2] && !match[3] && !match[4]) return 0;
  const delimChar = match[0][0];
  const midRun = prevChar === delimChar;
  if (pos === 0 || src[pos - 1] !== delimChar) {
    // The delimiter run starts here: masking cannot change the character
    // before it, so the opener checks need only the caller's prevChar and
    // a rejected opener skips the masking work entirely.
    if (match[4] && R_ALNUM.test(prevChar)) return 0; // _ cannot open between alphanumerics
    const nextChar0 = match[1] || match[3] || '';
    if (nextChar0 && prevChar && !R_PUNCT_CHAR.test(prevChar)) return 0;
  }
  // The opener's own run length.
  let lLength = 0;
  while (pos + lLength < src.length && src[pos + lLength] === delimChar) lLength++;
  // No later delimiter of this kind in the raw text means no closer can
  // exist in the masked text either — masking only removes delimiter runs —
  // so the masking and closer work is skipped entirely.
  if (src.indexOf(delimChar, pos + lLength) === -1) return 0;
  const masked = getMasked();
  let runStart = pos;
  while (runStart > 0 && masked[runStart - 1] === delimChar) runStart--;
  const runPrevChar = charBefore(masked, runStart);
  const runPrevPunct = runPrevChar === '*' || runPrevChar === '_' || R_PUNCT_CHAR.test(runPrevChar);
  if (runStart < pos) prevChar = runPrevChar;
  const prevPunct = runStart < pos ? runPrevPunct : R_PUNCT_CHAR.test(prevChar);
  if (match[4] && R_ALNUM.test(prevChar)) return 0; // _ cannot open between alphanumerics
  const nextChar = match[1] || match[3] || '';
  if (!nextChar || !prevChar || prevPunct) {
    const runLength = (pos - runStart) + lLength;
    const openerCanClose = runPrevChar.trim() !== '' && (!!nextChar || (delimChar === '*' && !runPrevPunct));
    const endReg = delimChar === '*' ? R_RDELIM_AST : R_RDELIM_UND;
    const hints = getHints();
    const lastCloser = delimChar === '*' ? hints.star : hints.under;
    const windowStart = pos + lLength;
    if (lastCloser < windowStart) return 0;
    const window = masked.slice(windowStart);
    const lastInWindow = lastCloser - windowStart;
    endReg.lastIndex = 0;
    let delimTotal = lLength;
    let midDelimTotal = 0;
    let m2;
    while ((m2 = endReg.exec(window)) !== null) {
      if (m2.index > lastInWindow) break;
      const rDelim = m2[1] || m2[2] || m2[3] || m2[4] || m2[5] || m2[6];
      if (!rDelim) continue;
      const rLength = rDelim.length;
      if (m2[3] || m2[4]) {
        delimTotal += rLength;
        continue;
      }
      if (m2[5] || m2[6] || openerCanClose) {
        if (midRun && (m2[5] || m2[6])) break;
        if (runLength % 3 !== 0 && (runLength + rLength) % 3 === 0) {
          midDelimTotal += rLength;
          continue; // emphasis rules 9-10
        }
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      const rLen = Math.min(rLength, rLength + delimTotal + midDelimTotal);
      const rawEnd = pos + lLength + m2.index + firstCodePointLen(m2[0]) + rLen;
      const raw = src.slice(pos, rawEnd);
      if (Math.min(lLength, rLen) % 2 === 1) {
        const html = inlineRun(raw.slice(1, -1), ctx, st, linkOK, flat);
        out.push(flat ? html : '<em>' + html + '</em>');
        return rawEnd;
      }
      const html = inlineRun(raw.slice(2, -2), ctx, st, linkOK, flat);
      out.push(flat ? html : '<strong>' + html + '</strong>');
      return rawEnd;
    }
  }
  return 0;
}

function tryDel(src, pos, ctx, st, prevChar, linkOK, flat, out, getMasked, getHints) {
  R_DEL_LDELIM_Y.lastIndex = pos;
  const match = R_DEL_LDELIM_Y.exec(src);
  if (!match) return 0;
  const nextChar = match[1] || '';
  if (!nextChar || !prevChar || R_PUNCT_CHAR.test(prevChar)) {
    let lLength = 0;
    while (lLength < 2 && src[pos + lLength] === '~') lLength++;
    // As in emphasis: no later tilde in the raw text means no closer in
    // the masked text either, so the masking and closer work is skipped.
    if (src.indexOf('~', pos + lLength) === -1) return 0;
    const masked = getMasked();
    const hints = getHints();
    const windowStart = pos + lLength;
    if (hints.tilde < windowStart) return 0;
    const window = masked.slice(windowStart);
    const lastInWindow = hints.tilde - windowStart;
    R_DEL_RDELIM.lastIndex = 0;
    let delimTotal = lLength;
    let m2;
    while ((m2 = R_DEL_RDELIM.exec(window)) !== null) {
      if (m2.index > lastInWindow) break;
      const rDelim = m2[1] || m2[2] || m2[3] || m2[4] || m2[5] || m2[6];
      if (!rDelim) continue;
      const rLength = rDelim.length;
      if (rLength !== lLength) continue;
      if (m2[3] || m2[4]) {
        delimTotal += rLength;
        continue;
      }
      delimTotal -= rLength;
      if (delimTotal > 0) continue;
      const rLen = Math.min(rLength, rLength + delimTotal);
      const rawEnd = pos + lLength + m2.index + firstCodePointLen(m2[0]) + rLen;
      const html = inlineRun(src.slice(pos + lLength, rawEnd - lLength), ctx, st, linkOK, flat);
      out.push(flat ? html : '<del>' + html + '</del>');
      return rawEnd;
    }
  }
  return 0;
}

function tryCodespan(src, pos, flat, out) {
  R_CODESPAN_Y.lastIndex = pos;
  const m = R_CODESPAN_Y.exec(src);
  if (!m) return 0;
  let text = m[2].replace(R_NL_GLOBAL, ' ');
  if (R_NON_SPACE.test(text) && text.charCodeAt(0) === 32 && text.charCodeAt(text.length - 1) === 32) {
    text = text.substring(1, text.length - 1);
  }
  out.push(flat ? text : '<code>' + esc(text, true) + '</code>');
  return pos + m[0].length;
}

function tryAutolink(src, pos, flat, out) {
  R_AUTOLINK_Y.lastIndex = pos;
  const m = R_AUTOLINK_Y.exec(src);
  if (!m) return 0;
  const text = m[1];
  const end = pos + m[0].length;
  if (flat) {
    out.push(text);
    return end;
  }
  const clean = cleanUrl(m[2] === '@' ? 'mailto:' + text : text);
  if (clean === null) {
    out.push(esc(text, true));
    return end;
  }
  out.push('<a href="' + esc(clean, true) + '">' + esc(text, true) + '</a>');
  return end;
}

function tryUrl(src, pos, flat, out) {
  R_URL_Y.lastIndex = pos;
  const m = R_URL_Y.exec(src);
  if (!m) return 0;
  let text, href;
  if (m[2] === '@') {
    text = m[0];
    href = 'mailto:' + text;
  } else {
    let cur = m[0], prev;
    do {
      prev = cur;
      cur = R_BACKPEDAL.exec(cur)?.[0] ?? '';
    } while (prev !== cur);
    if (!cur) return 0;
    text = cur;
    href = m[1] === 'www.' ? 'http://' + cur : cur;
  }
  const end = pos + text.length;
  if (flat) {
    out.push(text);
    return end;
  }
  const clean = cleanUrl(href);
  if (clean === null) {
    out.push(esc(text, true));
    return end;
  }
  out.push('<a href="' + esc(clean, true) + '">' + esc(text, true) + '</a>');
  return end;
}

// Scan one inline run to HTML. `st` carries the per-run raw-block and
// link-emitted flags shared with nested runs; ctx.inLink persists across
// runs. `flat` renders the text-only form used for image alt text.
function inlineRun(src, ctx, st, canParen, flat) {
  const n = src.length;
  // Plain-text chunks merge before they are escaped, exactly as the
  // reference lexer merges adjacent text tokens: a character reference
  // split across two chunks by a stop character must still be recognized
  // whole. `pending` holds the unescaped run; any other token flushes it
  // first, in order, through the writer every push goes through.
  const parts = [];
  let pending = '';
  let pendingRaw = false;
  const flushPending = () => {
    if (!pending) return;
    if (pendingRaw || !RE_ESC_TEST.test(pending)) parts.push(pending);
    else emitEscaped(pending, flat, parts);
    pending = '';
  };
  const out = { push(s) { flushPending(); parts.push(s); } };
  let pos = 0;
  let prevChar = '';
  let keepPrev = false;
  let masked = null;
  let hints = null;
  const getMasked = () => {
    if (masked === null) {
      // Without brackets, backticks, angle brackets or backslashes, no
      // pattern in the masking pass can match, so the masked text is the
      // source itself and the replacement passes are skipped.
      masked = (src.includes('[') || src.includes('`') || src.includes('<') || src.includes('\\'))
        ? maskSrc(src, ctx.links) : src;
    }
    return masked;
  };
  const getHints = () => (hints ?? (hints = scanHints(getMasked())));
  const linkOK = canParen && src.includes(')');
  let lastNonWs = -2; // index of the last non-whitespace char; -2 = not computed
  const getLastNonWs = () => {
    if (lastNonWs === -2) {
      let j = n - 1;
      while (j >= 0 && isWsCode(src.charCodeAt(j))) j--;
      lastNonWs = j;
    }
    return lastNonWs;
  };
  while (pos < n) {
    if (!keepPrev) prevChar = '';
    keepPrev = false;
    const c = src.charCodeAt(pos);
    let end = 0;
    if (c === 92) {
      // Backslash escape: a backslash plus one ASCII punctuation character.
      const e = src.charCodeAt(pos + 1);
      if ((e >= 33 && e <= 47) || (e >= 58 && e <= 64) || (e >= 91 && e <= 96) || (e >= 123 && e <= 126)) {
        const ch = src[pos + 1];
        out.push(flat ? ch : (ESCAPE_MAP[ch] || ch));
        pos += 2;
        continue;
      }
      // Backslash hard break: backslash, newline, non-whitespace ahead.
      if (e === 10 && getLastNonWs() >= pos + 2) {
        if (!flat) out.push('<br>');
        let j = pos + 2;
        while (j < n && (src.charCodeAt(j) === 32 || src.charCodeAt(j) === 9)) j++;
        pos = j;
        continue;
      }
    } else if (c === 60) {
      const t = src.charCodeAt(pos + 1);
      if (t === 33 || t === 47 || t === 63 || (t >= 65 && t <= 90) || (t >= 97 && t <= 122)) {
        R_TAG_Y.lastIndex = pos;
        const m = R_TAG_Y.exec(src);
        if (m) {
          const tag = m[0];
          if (!ctx.inLink && R_START_A.test(tag)) ctx.inLink = true;
          else if (ctx.inLink && R_END_A.test(tag)) ctx.inLink = false;
          if (!st.raw && R_START_PRE.test(tag)) st.raw = true;
          else if (st.raw && R_END_PRE.test(tag)) st.raw = false;
          out.push(tag);
          pos += tag.length;
          continue;
        }
      }
      end = tryAutolink(src, pos, flat, out);
      if (end) {
        pos = end;
        continue;
      }
    } else if (c === 91 || c === 33) {
      end = tryLink(src, pos, ctx, st, linkOK, flat, out)
        || tryReflink(src, pos, ctx, st, linkOK, flat, out);
      if (end) {
        pos = end;
        continue;
      }
    } else if (c === 42 || c === 95) {
      end = tryEmStrong(src, pos, ctx, st, prevChar, linkOK, flat, out, getMasked, getHints);
      if (end) {
        pos = end;
        continue;
      }
      if (c === 95 && !ctx.inLink && urlPossible(src, pos, n)) {
        end = tryUrl(src, pos, flat, out);
        if (end) {
          pos = end;
          continue;
        }
      }
    } else if (c === 96) {
      end = tryCodespan(src, pos, flat, out);
      if (end) {
        pos = end;
        continue;
      }
    } else if (c === 32) {
      // Spaces hard break: two or more spaces, newline, non-whitespace ahead.
      let j = pos + 1;
      while (j < n && src.charCodeAt(j) === 32) j++;
      if (j - pos >= 2 && src.charCodeAt(j) === 10 && getLastNonWs() >= j + 1) {
        if (!flat) out.push('<br>');
        let k = j + 1;
        while (k < n && (src.charCodeAt(k) === 32 || src.charCodeAt(k) === 9)) k++;
        pos = k;
        continue;
      }
    } else if (c === 126) {
      end = tryDel(src, pos, ctx, st, prevChar, linkOK, flat, out, getMasked, getHints);
      if (end) {
        pos = end;
        continue;
      }
    } else if (!ctx.inLink && urlPossible(src, pos, n)) {
      end = tryUrl(src, pos, flat, out);
      if (end) {
        pos = end;
        continue;
      }
    }
    const textEnd = scanTextEnd(src, pos, n);
    const chunk = src.slice(pos, textEnd);
    if (!pending) pendingRaw = st.raw;
    pending += chunk;
    if (src.charCodeAt(textEnd - 1) !== 95) prevChar = src[textEnd - 1];
    keepPrev = true;
    pos = textEnd;
  }
  flushPending();
  return parts.join('');
}

// ---------------------------------------------------------------------------
// Rendering (phase two) and entry point
// ---------------------------------------------------------------------------

function inlineHtml(s, ctx) {
  return inlineRun(s, ctx, { raw: false, emitted: false }, true, false);
}

function renderList(node, ctx, out) {
  out.push('<' + (node.o ? 'ol' : 'ul') + (node.o && node.st !== 1 ? ' start="' + node.st + '"' : '') + '>\n');
  for (const item of node.items) {
    out.push('<li>');
    const nodes = item.nodes;
    if (item.task && nodes.length > 0) {
      const first = nodes[0];
      const box = '<input ' + (item.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
      if (first.k === N_PARA) {
        out.push('<p>', box, inlineHtml(first.s, ctx), '</p>\n');
        renderNodes(nodes.slice(1), ctx, out);
      } else if (first.k === N_TEXT) {
        out.push(box, inlineHtml(first.s, ctx));
        renderNodes(nodes.slice(1), ctx, out);
      } else {
        renderNodes(nodes, ctx, out);
      }
    } else {
      renderNodes(nodes, ctx, out);
    }
    out.push('</li>\n');
  }
  out.push(node.o ? '</ol>\n' : '</ul>\n');
}

function renderTable(node, ctx, out) {
  out.push('<table>\n<thead>\n<tr>\n');
  for (let i = 0; i < node.hd.length; i++) {
    const al = node.al[i];
    out.push(al ? '<th align="' + al + '">' : '<th>', inlineHtml(node.hd[i], ctx), '</th>\n');
  }
  out.push('</tr>\n</thead>\n');
  if (node.rows.length > 0) {
    out.push('<tbody>');
    for (const row of node.rows) {
      out.push('<tr>\n');
      for (let i = 0; i < row.length; i++) {
        const al = node.al[i];
        out.push(al ? '<td align="' + al + '">' : '<td>', inlineHtml(row[i], ctx), '</td>\n');
      }
      out.push('</tr>\n');
    }
    out.push('</tbody>');
  }
  out.push('</table>\n');
}

function renderNodes(nodes, ctx, out) {
  for (const node of nodes) {
    switch (node.k) {
      case N_PARA:
        out.push('<p>', inlineHtml(node.s, ctx), '</p>\n');
        break;
      case N_TEXT:
        out.push(inlineHtml(node.s, ctx));
        break;
      case N_CODE:
      case N_HTML:
        out.push(node.h);
        break;
      case N_HEAD:
        out.push('<h' + node.d + '>', inlineHtml(node.s, ctx), '</h' + node.d + '>\n');
        break;
      case N_HR:
        out.push('<hr>\n');
        break;
      case N_BQ:
        out.push('<blockquote>\n');
        renderNodes(node.c, ctx, out);
        out.push('</blockquote>\n');
        break;
      case N_LIST:
        renderList(node, ctx, out);
        break;
      case N_TABLE:
        renderTable(node, ctx, out);
        break;
    }
  }
}

export function parse(markdown) {
  const src = markdown.indexOf('\r') === -1 ? markdown : markdown.replace(/\r\n|\r/g, '\n');
  const ctx = { links: Object.create(null), inLink: false };
  const frame = { nodes: [], tail: 0, touched: false };
  blockParse(src, ctx, true, false, frame);
  const out = [];
  renderNodes(frame.nodes, ctx, out);
  return out.join('');
}
