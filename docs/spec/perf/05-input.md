# 05. Read and parse

The Arena gives each kernel an NDJSON export, and it counts the parse. So the parse of NDJSON is part of each external target. The `.rlb` format of spec 07.2 does not help on the Arena, because the Arena does not give a `.rlb` file. This section makes the parse of NDJSON fast. The rules of spec 07.1 for a valid export do not change: each line that the fast path cannot read goes to the general parser.

## 05.1 The cost today

From 03.2 and 03.3, on Init:

- 28.1 G instructions for 348 MB and 6.5 M lines. This is 81 instructions for each byte.
- 49.7% is the general JSON scan: each object is scanned key by key, each key is found in a table of keys (`keys::code`), and each value is skipped and then read again.
- 30.5% is the probe of the intern table.
- SHA-256 is 2.4%. It already uses the SHA instructions of the CPU.

## 05.2 Budget

The budget for Init is 4.0 G for the parse and the intern, and 0.5 G for the read and the hash (04.10). This is about 11.5 instructions for each byte, and about 620 for each line. The budget for Mathlib (5.9 GB) is then about 71 G for the parse and about 30 G for the intern [U].

## 05.3 Template fast path

Each line of lean4export has one of a small number of forms. The keys are in alphabetical order, and each kind has a fixed layout (03.3). For example:

```
{"app":{"arg":1,"fn":7},"ie":8}
{"ie":40,"lam":{"binderInfo":"default","body":39,"name":12,"type":37}}
{"in":1,"str":{"pre":0,"str":"Subtype"}}
{"in":9,"num":{"i":0,"pre":8}}
{"const":{"name":1,"us":[1]},"ie":9}
```

The fast path is:

1. Compare the first bytes of the line with the fixed prefix of each form. The first two to eight bytes select the form: `{"app":{"arg":` selects `app`, `{"ie":` selects a binder or a `let`, and so on.
2. Read each number with a loop over the digits. Then compare the bytes between the numbers with the fixed text of the form, for example `,"fn":`.
3. If each fixed text matches and the line ends at `}`, the line is read. If a byte does not match, the general parser reads the line from the start. So the fast path never accepts a line that the general parser rejects, and it gives the same result on each line that it accepts.

The forms of the fast path are `app`, `lam`, `forallE`, `letE`, `bvar`, `sort`, `const`, `str` (name), `num` (name), `succ`, `max`, `imax`, `param` (level), `natVal`, `strVal` and `proj`. The declarations and the inductive types stay in the general parser. They are less than 1% of the lines.

Strings use the fast path only when they have no escape. A string with a backslash goes to the general parser.

A test reads each line of the corpus of spec 11 with the two parsers and compares the results. A fuzz target compares the two parsers on random lines.

A line that must grow an index table goes to the general parser too. The general parser checks the memory budget after the store call, and the store call changes the size of the store. So the fast path cannot do the same check before the call. This occurs about 50 times on Init, once for each doubling of one of the three tables.

Result on Init, on 2026-11-26 (`rulean check --parse-only`, macOS, `/usr/bin/time -l`): 27.97 G instructions and 9.03 G cycles before, 10.85 G instructions and 5.27 G cycles with the fast path. The counts of nodes, names and levels do not change.

The digit loop reads a slice of at most 19 bytes with a local index, and it computes `10 * v` with two shifts. The release build has overflow checks, so a multiply has a check and a branch, and the shifts have only the check of the add. With this loop, Init uses 10.50 G instructions (the smallest of three runs).

The compare of a fixed text reads 8 bytes of the line as one word and compares it with 8 bytes of the text. Each fixed text is a constant at its call, so after inlining the words of the text are constants too. With this compare and the room in the table of 05.5, Init uses 8.86 G instructions (the smallest of three runs).

## 05.4 Ids

The id of each kind (`ie`, `in`, `il`) goes up by one from line to line in each export that we know. The index from an export id to a store handle (`Index` in `ndjson.rs`) stays an array. The fast path adds one check: if the id is the next id, the handle goes at the end of the array, with no check of the array length. An id that is not the next id uses the general path, which is valid for each order.

## 05.5 Intern on input

The input nodes are already shared by lean4export: two equal nodes have one id in most cases [U]. The parse still interns each node, because the store needs one handle for each distinct term (spec 04.2).

The report has the counts of the walks of the expression tables (`probes` in the JSON report). On Init, on 2026-11-26:

| Run | Walks | Slots read | Full compares | Hits |
|---|---|---|---|---|
| `rulean check --engine R` | 218683678 | 253078632 | 113477406 | 110761375 |

So a walk reads 1.16 slots on average, and only 2.7 M full compares do not find the node. The table does not cluster, and equal hashes are rare. The probe is in the time profile of 03.3 because each walk reads a random slot of a large table, and this read often misses the cache. The Arena counts instructions, not cycles. So a change of the table does not give a large gain on the Arena measure. The instructions of the parse are in the scan of JSON (05.3). The parse of Init uses 27.97 G instructions and 9.03 G cycles, which is 3.1 instructions in each cycle.

A change of the table is still useful for the wall time (G5). The candidates are a prefetch of the slot for the next line, and nodes of one kind in one array of 8 or 12 bytes. These are not in M8.

The table of the frozen expressions doubles when it is half full, and each doubling puts each node in the table again. On Init the table doubles 20 times, and the doublings and the fills of the new tables use about 0.6 G in the profile of the parse. So before the parse, `rulean check` estimates the count of the nodes from the size of the file, at 64 bytes for each node (Init has about 57), and makes the table that large (`Store::reserve_exprs`). The estimate is a little low for an export like Init, so the table has the same size at the end as with no estimate. The call does nothing if the estimate puts the store over its memory budget. With the estimate, Init uses 9.69 G instructions (the smallest of three runs), and the bytes of the store do not change.

## 05.6 Read and hash

The file is read with `mmap` when the OS allows it, and with one `read` into one buffer if not. SHA-256 runs on the same buffer in one pass. On Init the read and the hash use about 0.7 G (4.2% and 2.4% of 28.1 G). They can overlap with the parse on a second thread. This does not reduce the instructions. It reduces the wall time (G5).

## 05.7 Threads

Kontroli found that a parallel parse with channels did not help (02.7). A parse on more than one thread needs a split of the input at a line boundary and a merge of the handles, and the lines refer to earlier lines. So the parse stays on one thread. The check starts when the first declaration is read, on the other threads (spec 08.3). This gives the wall time without a parallel parse.

## 05.8 What does not change

- The rules of spec 07.1: each error that the general parser finds, the fast path also finds, because the fast path gives each line that it does not fully match to the general parser.
- The limits of spec 05.11 and 12.
- The `.rlb` format. It stays a cache for local use.
