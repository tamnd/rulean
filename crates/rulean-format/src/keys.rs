//! The codes of the JSON keys that the format uses.
//!
//! Each key has one code, in all record kinds. `Obj::vals` is indexed by this code.

pub const META: usize = 0;
pub const IN: usize = 1;
pub const IL: usize = 2;
pub const IE: usize = 3;
pub const AXIOM: usize = 4;
pub const DEF: usize = 5;
pub const OPAQUE: usize = 6;
pub const THM: usize = 7;
pub const QUOT: usize = 8;
pub const INDUCTIVE: usize = 9;
pub const STR: usize = 10;
pub const NUM: usize = 11;
pub const SUCC: usize = 12;
pub const MAX: usize = 13;
pub const IMAX: usize = 14;
pub const PARAM: usize = 15;
pub const BVAR: usize = 16;
pub const SORT: usize = 17;
pub const CONST: usize = 18;
pub const APP: usize = 19;
pub const LAM: usize = 20;
pub const FORALL_E: usize = 21;
pub const LET_E: usize = 22;
pub const PROJ: usize = 23;
pub const NAT_VAL: usize = 24;
pub const STR_VAL: usize = 25;
pub const MDATA: usize = 26;
pub const PRE: usize = 27;
pub const I: usize = 28;
pub const NAME: usize = 29;
pub const US: usize = 30;
pub const FN: usize = 31;
pub const ARG: usize = 32;
pub const BINDER_INFO: usize = 33;
pub const BODY: usize = 34;
pub const TYPE: usize = 35;
pub const NONDEP: usize = 36;
pub const VALUE: usize = 37;
pub const IDX: usize = 38;
pub const STRUCT: usize = 39;
pub const TYPE_NAME: usize = 40;
pub const EXPR: usize = 41;
pub const DATA: usize = 42;
pub const ALL: usize = 43;
pub const HINTS: usize = 44;
pub const IS_UNSAFE: usize = 45;
pub const LEVEL_PARAMS: usize = 46;
pub const SAFETY: usize = 47;
pub const KIND: usize = 48;
pub const REGULAR: usize = 49;
pub const TYPES: usize = 50;
pub const CTORS: usize = 51;
pub const RECS: usize = 52;
pub const IS_REC: usize = 53;
pub const IS_REFLEXIVE: usize = 54;
pub const NUM_INDICES: usize = 55;
pub const NUM_NESTED: usize = 56;
pub const NUM_PARAMS: usize = 57;
pub const CIDX: usize = 58;
pub const INDUCT: usize = 59;
pub const NUM_FIELDS: usize = 60;
pub const K: usize = 61;
pub const NUM_MINORS: usize = 62;
pub const NUM_MOTIVES: usize = 63;
pub const RULES: usize = 64;
pub const CTOR: usize = 65;
pub const NFIELDS: usize = 66;
pub const RHS: usize = 67;
pub const EXPORTER: usize = 68;
pub const LEAN: usize = 69;
pub const FORMAT: usize = 70;
pub const VERSION: usize = 71;

/// The number of known keys.
pub const COUNT: usize = 72;

/// The code of the key `k`, or `COUNT` if the format does not use the key.
///
/// The function selects a group by the first byte and then compares the bytes. Aeneas does not translate a `match` on byte-string patterns, so the code does not use one.
pub fn code(k: &[u8]) -> usize {
    if k.len() == 0 {
        return COUNT;
    }
    let mut r = COUNT;
    match k[0] {
        b'a' => {
            if same(k, b"axiom") {
                r = AXIOM;
            }
            if same(k, b"app") {
                r = APP;
            }
            if same(k, b"arg") {
                r = ARG;
            }
            if same(k, b"all") {
                r = ALL;
            }
        }
        b'b' => {
            if same(k, b"bvar") {
                r = BVAR;
            }
            if same(k, b"binderInfo") {
                r = BINDER_INFO;
            }
            if same(k, b"body") {
                r = BODY;
            }
        }
        b'c' => {
            if same(k, b"const") {
                r = CONST;
            }
            if same(k, b"ctors") {
                r = CTORS;
            }
            if same(k, b"cidx") {
                r = CIDX;
            }
            if same(k, b"ctor") {
                r = CTOR;
            }
        }
        b'd' => {
            if same(k, b"def") {
                r = DEF;
            }
            if same(k, b"data") {
                r = DATA;
            }
        }
        b'e' => {
            if same(k, b"expr") {
                r = EXPR;
            }
            if same(k, b"exporter") {
                r = EXPORTER;
            }
        }
        b'f' => {
            if same(k, b"forallE") {
                r = FORALL_E;
            }
            if same(k, b"fn") {
                r = FN;
            }
            if same(k, b"format") {
                r = FORMAT;
            }
        }
        b'h' => {
            if same(k, b"hints") {
                r = HINTS;
            }
        }
        b'i' => {
            if same(k, b"in") {
                r = IN;
            }
            if same(k, b"il") {
                r = IL;
            }
            if same(k, b"ie") {
                r = IE;
            }
            if same(k, b"inductive") {
                r = INDUCTIVE;
            }
            if same(k, b"imax") {
                r = IMAX;
            }
            if same(k, b"i") {
                r = I;
            }
            if same(k, b"idx") {
                r = IDX;
            }
            if same(k, b"isUnsafe") {
                r = IS_UNSAFE;
            }
            if same(k, b"isRec") {
                r = IS_REC;
            }
            if same(k, b"isReflexive") {
                r = IS_REFLEXIVE;
            }
            if same(k, b"induct") {
                r = INDUCT;
            }
        }
        b'k' => {
            if same(k, b"kind") {
                r = KIND;
            }
            if same(k, b"k") {
                r = K;
            }
        }
        b'l' => {
            if same(k, b"lam") {
                r = LAM;
            }
            if same(k, b"letE") {
                r = LET_E;
            }
            if same(k, b"levelParams") {
                r = LEVEL_PARAMS;
            }
            if same(k, b"lean") {
                r = LEAN;
            }
        }
        b'm' => {
            if same(k, b"meta") {
                r = META;
            }
            if same(k, b"max") {
                r = MAX;
            }
            if same(k, b"mdata") {
                r = MDATA;
            }
        }
        b'n' => {
            if same(k, b"num") {
                r = NUM;
            }
            if same(k, b"natVal") {
                r = NAT_VAL;
            }
            if same(k, b"name") {
                r = NAME;
            }
            if same(k, b"nondep") {
                r = NONDEP;
            }
            if same(k, b"numIndices") {
                r = NUM_INDICES;
            }
            if same(k, b"numNested") {
                r = NUM_NESTED;
            }
            if same(k, b"numParams") {
                r = NUM_PARAMS;
            }
            if same(k, b"numFields") {
                r = NUM_FIELDS;
            }
            if same(k, b"numMinors") {
                r = NUM_MINORS;
            }
            if same(k, b"numMotives") {
                r = NUM_MOTIVES;
            }
            if same(k, b"nfields") {
                r = NFIELDS;
            }
        }
        b'o' => {
            if same(k, b"opaque") {
                r = OPAQUE;
            }
        }
        b'p' => {
            if same(k, b"param") {
                r = PARAM;
            }
            if same(k, b"proj") {
                r = PROJ;
            }
            if same(k, b"pre") {
                r = PRE;
            }
        }
        b'q' => {
            if same(k, b"quot") {
                r = QUOT;
            }
        }
        b'r' => {
            if same(k, b"regular") {
                r = REGULAR;
            }
            if same(k, b"recs") {
                r = RECS;
            }
            if same(k, b"rules") {
                r = RULES;
            }
            if same(k, b"rhs") {
                r = RHS;
            }
        }
        b's' => {
            if same(k, b"str") {
                r = STR;
            }
            if same(k, b"succ") {
                r = SUCC;
            }
            if same(k, b"sort") {
                r = SORT;
            }
            if same(k, b"strVal") {
                r = STR_VAL;
            }
            if same(k, b"struct") {
                r = STRUCT;
            }
            if same(k, b"safety") {
                r = SAFETY;
            }
        }
        b't' => {
            if same(k, b"thm") {
                r = THM;
            }
            if same(k, b"type") {
                r = TYPE;
            }
            if same(k, b"typeName") {
                r = TYPE_NAME;
            }
            if same(k, b"types") {
                r = TYPES;
            }
        }
        b'u' => {
            if same(k, b"us") {
                r = US;
            }
        }
        b'v' => {
            if same(k, b"value") {
                r = VALUE;
            }
            if same(k, b"version") {
                r = VERSION;
            }
        }
        _ => {}
    }
    r
}

/// True if the byte strings are equal.
fn same(a: &[u8], b: &[u8]) -> bool {
    let mut eq = a.len() == b.len();
    let mut i = 0;
    while eq && i < a.len() {
        eq = a[i] == b[i];
        i += 1;
    }
    eq
}
