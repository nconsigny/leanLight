<!-- Copied verbatim from leanKohakuDesktop (private) spec/16-light-client.md at 7a491530 on 2026-10-29. Sections on the wallet (lkd-lc, netd, keyd, the UI, Tor) describe how the wallet runs this light client; leanLight is the generic part. Links to other spec/ files point into that repository. -->

# 16 - Light client

**Status: LC0 to LC9 built and proved as each milestone's As built says (2026-10-27)**
([LC9: the design as decided](#lc9-the-design-as-decided), [as built](#as-built-lc9); its live
run's verdicts in [Milestones](#milestones)). It
replaces the a37cf09 proposal, and amends `00-plan.md` decision 5, the opening of
`04-verified-reads.md`, `AGENTS.md`'s Runtime Lean rules (open decisions 6, 13, 14), invariants
10, 14b, 19a, 19b and the journal codec row, and `06-tor.md`'s third-party rule (open decision
23) ([Other documents](#other-documents-in-the-same-changes)).

The wallet follows Ethereum's sync committee with a light client of its own, written in Lean
and run as compiled Lean, under the [Runtime Lean rules](../AGENTS.md#runtime-lean), in a
sandboxed process of its own, `lkd-lc`. Like helios it verifies the answers the wallet reads,
not only headers. Unlike helios it anchors only on headers that at least two thirds of the
committee (342 of 512) signed, halts on a conflict and keeps the evidence, compares several
sources, and binds every ETH balance and nonce the wallet shows or decides on, the code of the
contracts it sends to, token balances, pool roots and the inclusion of what it sent: v1 is G1
to G12 without G13, plus G14 to G16 ([the table](#why-and-helios)). LC9 adds the account at the
finalized block (G11's "settled at block F, final" and D7's outcome 1), the reorg check of the
blocks shown batches were proved at (G9), ENS names and prices read at the anchor, the selected
account's primary name kept as facts (G19), and the UI's halves of the composed theorems.

This replaces the proposal of a37cf09 entirely. What changed, and why:

| a37cf09 proposed | Now | Why |
|---|---|---|
| Rust in `lkd-verified`, refined by Aeneas; "BLS in compiled Lean would not be [fast enough]" | Lean (`LkdLc`), compiled by Lean core's compiler; the code that runs is what the theorems are about | Measured on 2026-10-24: about 10 ms to verify an update and about 0.44 s (`[r]P`) to check a committee, against that proposal's budgets of 200 ms and 2 s ([Speed](#speed)); the user's decision 1 |
| `netd` and the UI both run it | `lkd-lc`, one per machine; netd, the UI and the launcher link no Lean | netd keeps one thread and its kill filter; the UI keeps its `EPERM` filter; BLS runs once; the CLI asks the daemon ([Placement](#placement)). **Cost**: every green value now rests on `lkd-lc` (H_lc), where a37cf09's UI re-ran the light client itself: one exploit in its parsers, runtime, GMP or shim, reached through bytes netd forwards from any beacon source, can paint every value green. Mitigations: the UI's re-check and the head cross-check ([What the UI trusts](#processes-and-trust-boundary)) |
| Gloas later (LC7); Sepolia unanchored meanwhile | Gloas in v1 | Gloas has been live on Sepolia since 2026-10-06 13:53:36 UTC, and Tornado on Sepolia is the default |
| `eth_getBlockByNumber(N)` then `execution_matches` | The EL header by hash; each hash tagged as the block's own or its parent's, by its header's own slot | A Gloas light-client header carries only `execution_block_hash`, the parent payload's hash |
| Headers and the selected account | Also every ETH balance and nonce (G10, G11), code-hash pins (G14), token balances (G15), pool roots (G16), inclusion and receipt status (G12) | The user's decision 3 |
| The evidence written by netd in its mount view | Written in place by `lkd-lc`, through a descriptor opened before its sandbox | netd has no file access, and its seccomp filter kills `open` |
| SSZ only; a source that does not serve it is not used | Every check runs on SSZ bytes; netd may re-encode JSON to SSZ, untrusted | A public Lighthouse endpoint answered JSON to `Accept: application/octet-stream` |
| SSZ, BLS and SHA-256 written from scratch | Reused where a Lean source exists: ssz-specs for SSZ and the runtime SHA-256, EthLib as the readable BLS layer, Mathlib's fields, the Yellow Paper trie model of `proof/mpt-trie` ([Sources](#sources)) | The user's decision 4; the reuse matrix of 2026-10-24 |
| Milestones LC1 to LC7 | LC0 to LC9 (LC4 in two) | The roadmap already uses M1 to M12 |

Adopting it amends three earlier decisions:

- [`00-plan.md`](00-plan.md) decision 5, whose first version said "responses are checked
  against a light client" and whose second amendment put the quorum in its place. Proposed
  third amendment: *state reads are checked against a light client of the wallet's own,
  compiled Lean in a process of its own (`lkd-lc`, [`16-light-client.md`](16-light-client.md));
  the quorum stays as the labelled fallback where the light client cannot answer.* The plan's
  process table gains `lkd-lc`, and its trust base gains Lean's compiler and runtime inside
  `lkd-lc` as it has them inside `keyd`.
- The opening of [`04-verified-reads.md`](04-verified-reads.md), "No helios and no light
  client": the chain of checks there keeps its header and Merkle steps, and the block hash
  comes from the light client instead of a quorum.

2026-10-28: the quorum is removed (the user's decision). Where the light client cannot answer,
the labelled fallback is one endpoint's head (the first that answers, the next one's when it
fails) or your node's, on its word, in yellow ([`04-verified-reads.md`](04-verified-reads.md)).
- The a37cf09 spec/16's placement and its open decisions 1 (BLS), 2 (process), 6 (refresh,
  open decision 7 here), 9 (encoding) and 11 (Gloas), decided here.

The documents and rules each change touches, `AGENTS.md` included, are listed under
[Other documents](#other-documents-in-the-same-changes).

`keyd` decides nothing new: it takes no reads (N3), and nothing of `LkdLc` is linked into it.
Two changes reach it, each with the review `AGENTS.md` asks for: its shell decodes and stores
one more journal record kind (G12; the storage review), and, with the base library and the
shared runtime crate (open decisions 13 and 14), its build links `lkdbase` and `lkd-lean-rt`
(the ABI review).

Sizes: S at most a week, M one to three weeks, L one to two months, for one engineer.

## What we reuse instead of writing

The user's decision 4 asked that nothing a Lean library already has be written again. The
reuse matrix of 2026-10-24 (`scratch-lc/research/reuse.md`: rows C1 to C13, in-tree rules D1
to D19) checked VCVio, Mathlib, Lean core and some thirty other Lean repositories; this design
follows it, with three departures (open decision 21). Pins, licences and the exact use of each
source are in [Sources](#sources).

| Need | Taken from | How |
|---|---|---|
| SHA-256 at runtime | ssz-specs' `Ssz/Hash/Sha256.lean` | Vendored into `LkdBase` with `get!` made `getD`, its five `@[csimp]` kept and `private` dropped, namespace `Ssz.Sha256` kept, the tree's one copy (built, LC3); the bench's copy dropped (C1b, D1) |
| SHA-256 specification | VCVio's `VCVio.Algorithms.Sha2` | Replaces lkd's vendored copies (D19, LC0) |
| SSZ specification, canonicality, branch binding, gindices | ssz-specs `lean/` | Vendored into `LkdProofs/Vendor/SszSpecs`, since it does not build as a dependency on 4.35 (the gate, [Sources](#sources)); the runtime roots, branches and gindices are proved equal to it, the decoders checked against it by vectors (C2, C3, D11, D12; built, LC3) |
| BLS12-381 readable code, the p and r certificate data, the G1 group law | EthLib | Vendored as the specification in `LkdProofs`; the bench's fast layer, which runs, is proved equal to it (C4b to C4h) |
| `Fp2`, `Fp6`, `Fp12` as fields; primality; the Weierstrass group law | Mathlib v4.35.0 | `QuadraticAlgebra` (no third hand-rolled `Fp2`, D6); `lucas_primality` (C4d to C4f) |
| Modular exponentiation | Lean core's `Nat.powMod` | At runtime and in proofs; three in-tree copies retired (C5a, D7) |
| The ordered trie root | The Yellow Paper's trie, Appendix D, as `Spec.Mpt.Trie` models it (`proof/mpt-trie`, with `Spec.Mpt.lookup` complete and sound on it) | The runtime builder is proved equal to its `root` (LC8, [as built](#inclusion-as-built-lc8-core)); leanerSTFSpec's `patricialize` (C8b) is not vendored: it brings a second RLP encoder (D3, D16) |
| Keccak, RLP, MPT proofs, block headers, the chain table | lkd's `LkdCore.Keccak`, `LkdCore.Rlp`, `Spec.Mpt`, `Spec.Header`, `Spec.Networks` | Kept: Keccak and RLP move into `LkdBase`, the MPT and header checks into `LkdLc.El`, and `Forks` is keyed on `Spec.Networks`; nothing is copied (D2, D3, D15, D17) |
| Pairing laws, where a theorem needs them | `Spec.Bn254`'s hypothesis shape | No axiom (D18) |

Written because no Lean source has them: the fast 381-bit field and BLS layer (from the
benchmark written for lkd), the typed SSZ decoders, the sync protocol, the normalized-branch
wrapper, the runtime trie builder, the EIP-2935, ERC-20 and EIP-1967 slot formulas, every proof
about a Miller loop, a final exponentiation or `clear_cofactor`, and the test-only Snappy.

**VCVio's role, plainly.** VCVio is a proof-only dependency of `LkdProofs`, pinned at
`88efe971` once the Lean 4.35 bump lands (LC0). Its FIPS 180-4 SHA-256 becomes `Spec.Sha256`,
in place of the copy lkd vendored from it, and its Keccak stays the specification
`LkdCore.Keccak` is proved equal to. Nothing of VCVio runs in the wallet: it imports Mathlib
and indexes with `!`, which the
Runtime Lean rules forbid. It has no SSZ, BLS12-381, pairing, sync protocol or trie
construction, so it spares none of the light client's runtime code; its Merkle binding theorems
are read, not imported, since only ssz-specs' binding is about a verifier that checks node
widths (C3, D11).

**Departures from the matrix** (open decision 21): EthLib's readable layer is a specification
in `LkdProofs`, not runtime code under `@[csimp]` as C4a and C4b had it, because its equalities
with the fast layer need Mathlib (open decision 6); CompElliptic is read, not ported (C4i),
because it has no licence file and its theorems are N7's subject; and the UI's Rust re-check
and netd's Rust reads stay beside `LkdLc.El`, where D3 asks for one implementation per check
([What the UI trusts](#processes-and-trust-boundary)).

## Open decisions, with recommendations

What the user approves; each row links to where it is argued. The user's binding decisions of
2026-10-24 (the light client in compiled Lean; turbo-lean and lean-native as development tools
only; v1's scope; reuse before writing) are not reopened. Decisions 3, 4, 5, 19, 22, 23, 25 and
26 were put to the user with LC7 and LC8's decision gate and answered on 2026-10-27, all as
recommended ([The decision gate](#the-decision-gate)); each row names its decision there (D1 to
D7) and what was built. LC9's gate ([The decision gate (LC9)](#the-decision-gate-lc9)) answered
decisions 6 (D54), 9 (D53, which decides 2 with it), 23's fallback within a session (D59) and 25's
names (D47, D48) on 2026-10-27. As built (LC9), each row is decided and built, or open with
what was built: rows 1, 8, 10, 12, 15 to 18, 20, 21 and 24 were never put to the user as
questions of their own and stand as recommended, built so. Row 29, the first checkpoint taken
without a question when every source agrees, and the light client on by default on public
routes, are the user's decisions of 2026-10-28 (after the light client's merge).

| # | Decision | Recommendation | What it costs the user | Where |
|---|---|---|---|---|
| 1 | JSON re-encoded to SSZ by netd, for sources that ignore SSZ | *Yes*, in LC6; a re-encoded `/updates` chunk carries the item's fork name, not a digest. **Open; built as recommended** (LC6, netd's `reencode`): Electra's and Fulu's objects only, Gloas's (which no JSON-only source serves) `NotSsz`; `lkd-lc` checks every byte as it checks a source's own SSZ | netd parses more untrusted JSON; a wrong re-encoding only fails the checks | [The beacon API](#the-beacon-api) |
| 2 | Default beacon sources | Two or more per chain where the survey finds them. **Decided with decision 9** (the user, 2026-10-27, LC9's D53) **and built** (`lkd init`'s suggestions, `init::SUGGESTED_BEACON`, from the survey of 2026-10-26): on mainnet ChainSafe's Lodestar, PublicNode (JSON, re-encoded) and the Nimbus team's node (plain HTTP over Tor); on Sepolia ethPandaOps' Nimbus route, then ChainSafe's Lodestar, which serves no bootstrap at a grid root since Gloas. Recommended on a public route; on a route to your own node an opt-in (decision 9). With one source the overview says "Light client from 1 beacon source, no cross-check" | On one source, conflicts across sources (G2) and comparison (G3) do not hold, and one operator sees every lkd's polling | [Sources, configured](#sources-configured) |
| 3 | A pin that does not match, or is not proved at the anchor | **Decided** (the user, 2026-10-27, as recommended: [D1](#decisions)) **and built** (LC7: one table, `lkd_ui::pins::act`, in the terminal UI, the window and the command line; 25w): by who holds the funds. Deposits (Tornado; Privacy Pools through the Entrypoint) and Privacy Pools withdrawals through `Entrypoint.relay` are blocked on any cause (the code or the implementation's code not the pinned one, a proxy upgraded, a condition gating the flow failed, unproved, not pinned), a blocked withdrawal naming ragequit as the exit; a Tornado relayed withdrawal is blocked on a code mismatch of the pool or of what it uses, and asks an acknowledgment naming the reason when unproved or not pinned; ragequit and a direct withdrawal ask an acknowledgment, never blocked; a stealth send is blocked on a Multicall3 mismatch, an acknowledgment otherwise; a token send and a registration ask an acknowledgment, the token red ([as built](#lc7-tokens-ui)) | A stalled light client, or your own reth node at its default proof window, blocks deposits and Privacy Pools relayed withdrawals, never ragequit or a direct withdrawal; an upgrade of the Privacy Pools Entrypoint blocks its deposits and relayed withdrawals until a release pins the new implementation; a review opened while a block body downloads may wait up to `PIN_BATCH_WITHIN` (67 s) for its batch; blocking a stealth send on a Multicall3 mismatch departs from decision 16 | [Code-hash pins](#code-hash-pins-g14) |
| 4 | Token proofs | **Decided** (the user, 2026-10-27, as recommended: [D2](#decisions)) **and built** (LC7, `lkd_ui::token_proofs`): the selected address, every pinned token in one batch (a batch never says which tokens it holds), on an explicit refresh and before a token send's review, at most once an epoch; the automatic refresh keeps `aggregate3`'s `balanceOf`, labelled the node's word, unless a proof younger than an epoch exists; another address once the user selects it. Token snapshots too (D22, the user's yes): `MakeTokenSnapshot` in the snapshot pass, for the selected address after a token proof, at most every 10 minutes | Other addresses' token balances stay unproved until selected; a token send's review waits for its batch | [Token balances](#token-balances-g15) |
| 5 | Included, then reorged | **Decided** (the user, 2026-10-27, as recommended: [D3](#decisions), with decision 19) **and built** (LC8, `lkd_ui::included`): nothing is kept that a reorg could undo. A proof is kept only when final, after the UI's re-check of its certificate and the head cross-check of the proving header; too old only when `keyd`'s `Sent.time` makes it plausible (sent more than 8191 slots and an hour before the anchor's slot time), else the node mislocated it and it is asked again; too large only as `lkd-lc` answers it after `maxAttempts` attempts, with two or more public endpoints or your own node; settled by nonce as decision 22 says; refusals never (red, backoff). A proof is never superseded by another outcome, and a later proof naming another block hash supersedes it; a refresh never reopens a record: one kept under an earlier checkpoint is shown "proved under an earlier checkpoint", and asked once more only after a checkpoint ceremony | One record kind more (the storage review); a refusal is asked again each session; with one public endpoint "too large" is never kept | [Inclusion](#inclusion-and-receipts-g12) |
| 6 | Fast versions proved equal in `LkdProofs`, not inside the Init-only closure | *Adopt*; amend `AGENTS.md`, with a second reviewer; every such equality listed in `Audit.lean`. **Decided** (the user, 2026-10-27, LC9's D54: described in `AGENTS.md` as the practice, not a rule) **and built**: LC4b's BLS layer against EthLib's in `LkdProofs`; the equalities that need only `Init` stay in the runtime module, each `csimp` equation listed in `Audit.lean` (`LkdBase.Sha256`'s, and LC9's merge of master's fast Keccak-256, `LkdBase.KeccakFast`, run by `keyd` and `lkd-lc`) | The code that runs is tied to its readable specification by a theorem outside the runtime package | [Fast code](#the-lean-package) |
| 7 | How the checkpoint is refreshed | *Automatically*: the launcher writes the grid root `lkd-lc --check` reaches within `MAX_AGE`, prints it and shows it in Settings; this amends a37cf09's open decision 6 ("the trust root changes only with the user's yes"), a yes that adds no trust. Otherwise: asked at every start from day 7, default yes, red from day 10. **Decided** ("build the refresh", 2026-10-26) **and built** (`lc6/refresh`): the core keeps the newest grid checkpoint it reached and its verified bootstrap in the evidence, `--check` prints it (`lkd_lc_reached`, 25h), the launcher writes it at a start when more than 7 days newer (`checkpoint_from = refreshed`), and the next `lkd-lc` starts from the kept bootstrap offline (25e, 25n); the overview's "Refresh needed" line from day 7, red from day 10, is built (LC6, `light::overview_lines`), the question at every start is not | Declined or missed refreshes end, 14 days after the checkpoint, in a new checkpoint ceremony; a wallet not running while a period's first epoch is finalized reaches no grid checkpoint for that period | [Refresh](#refresh) |
| 8 | The age bound `MAX_AGE` | *14 days, fixed*. **Built so** (LC5, `Forks.maxAge14d`; ten minutes on the development chain) | A user away longer than 14 days from the last refresh confirms a new checkpoint; a longer bound trusts an older committee, whose members may have exited, and widens G6's residual | [The age bound](#the-age-bound-max_age) |
| 9 | Own-node routes and public beacon sources | **Decided** (the user, 2026-10-27, LC9's [D53](#decisions-lc9): "opt-in on own-node routes", option (b) below) **and built** (`lc9/own-node`, [as built](#lc9-own-node)): on a route to your own node (IPC, TCP on `127.0.0.1` or an onion service, hybrid or not) the light client runs only with your own beacon node or with public beacon sources you opted in to. `lkd init`'s fourth question and `lkd settings`' Light client part recommend nothing there: they say first that with public beacon endpoints tor starts unless the wallet runs it already, and the beacon endpoints see when an lkd light client is online, never your addresses, about 7,200 small polls a day, and take them only after a yes that says it again (Enter alone: no); the review of `lkd settings` and of the window says it too when the route moves from public endpoints to your own node with public beacon sources kept. Without them: your own beacon node, or no light client and today's label "(proved at block N of your node)". On a public route public beacon sources stay what `lkd init` recommends, as tor runs anyway. The choice traded roadmap M4 ("private by default on your own node") against the user's decision 3: (a) public beacon sources by default, tor starting and beacon endpoints seeing when an lkd light client is online, never its addresses; (b) opt-in at `lkd init` and in `lkd settings`, with that notice | No consensus check on an own-node route without your own beacon node or the opt-in; the opt-in costs what (a) would have: tor (unless it runs already) and about 7,200 polls a day | [Sources, configured](#sources-configured) |
| 10 | A display freshness bound `F` | *2 epochs*: beyond it a value turns yellow, "proved at block N, 3 h ago". **Built so** (LC6, `light::fresh_ms`: 768 s on mainnet and Sepolia, 16 s on the development chain); LC9's D58 adds a bound for what gates or pays, `lc_check::gate_bound_s` (768 s, 90 s on the development chain) | Values turn yellow sooner when the light client stalls | [Labels](#processes-and-trust-boundary) |
| 11 | Which EL endpoint proves an address | *One public endpoint per address, kept* (index `keccak(address ‖ salt) mod n`, the salt random per install and written by `lkd init`); another only after a refusal or a timeout. **Built (LC6a)**: `upstream::endpoint_for`, the first 8 bytes of `keccak(key ‖ salt)` big-endian plus the request's `attempt`, mod `n`; the key is the address for `ElProof`, the block hash for `ElHeader`; netd's `--salt` (without it, one drawn per netd start: netd run by hand or by a test; `lkd` always passes one). **Fixed after the second review (2026-10-28)**: an install made before the light client (master's `lkd init` wrote no salt) gets its one salt when a beacon source is first configured, by `lkd settings` (written with the settings) or, failing that, by `lkd start`, which writes it to the configuration once before netd starts (`config::Light::fill_salt`), so netd is never left to draw one per start | An endpoint that refuses one address delays that address | [Every ETH balance](#every-eth-balance-g10), [Egress v8](#egress-v8-invariant-10i) |
| 12 | `clear_cofactor` for G2 | *`[h_eff]P`*, proved definitionally (N7's "definitional algorithms where the budget allows"); LC4a's acceptance 20 ms an update. Otherwise RFC 9380 G.3, with "G.3 equals `[h_eff]`" in H_vec. Built so in LC4a | About 5.1 ms more an update (about 17 ms); measured in LC4a, 5.65 ms, an update 17.0 ms | [Proved, checked by vectors, trusted](#proved-checked-by-vectors-trusted) |
| 13 | A base runtime library (reuse D15) | *Adopt* (the user's choice, 2026-10-25): `LkdBase` holds Keccak, RLP, SHA-256 and the byte helpers, imported by `LkdCore` and `LkdLc`. Otherwise a recorded departure from D15, with the helpers in `LkdCore.Rlp`. **Built** (LC1; since LC9 it holds the fast Keccak-256 too, `LkdBase.KeccakFast`) | A change to `keyd`'s build and ABI crate, with its second reviewer | [The Lean package](#the-lean-package) |
| 14 | One Lean runtime crate (reuse D14) | *Adopt* (the user's choice, 2026-10-25): `crates/lean-rt` holds the one `unsafe` runtime module, the shim's generic part and the toolchain link; and `lkd-lc`'s own sandbox calls go into `crates/sandbox/src/sys.rs`, so `crates/lc` has no `unsafe` module. Otherwise a reviewed exception, with a CI diff of the two generic parts, and `crates/lc/src/sys.rs` joins `AGENTS.md`'s list. **Built** (LC1) | The same review of `keyd`'s ABI crate, and of `crates/sandbox/src/sys.rs` | [FFI and the runtime](#ffi-and-the-runtime) |
| 15 | A conflict on a next committee | *Halt*, as on a finalized block. **Built so** (LC5, `Store.conflict`, 25g) | An honest deep fork across a period boundary stops the light client until a new checkpoint | [Conflicts](#conflicts-g2) |
| 16 | Sending in every state | *Yes*: `keyd` checks nothing it reads; the review says what is proved. **Built so**, but for what D1, D46 and D60 gate: deposits and Privacy Pools relayed withdrawals block when unproved | A send from an unproved balance is possible, and said | [Failure states](#failure-states) |
| 17 | The foreign-nonce alarm's colour | *Red* for a keystore account; *yellow*, "not signed by lkd", for hardware-wallet and seed accounts, since another wallet may hold the key (a restore cannot be detected). **Built so** (LC2 and LC6: red only for an anchored nonce of a keystore account, `proved::alarm_line`) | No red alarm for seed accounts | [The alarm](#the-foreign-nonce-alarm) |
| 18 | A head cross-check against the EL route | *Adopt*: for each anchor number `N` shown, `eth_getBlockByNumber(N, false)` on `Head`; a different hash at or below the finalized number is a red "verifier disagreement", above it a yellow "your node disagrees at block N (not final)". **Built** (LC6; by header, `HeaderAt`, D35 in LC7; behind every balance, token, pin, pool, inclusion, name and price since LC9, and D39's free check) | One request per anchor change; a green lie then needs `lkd-lc` and the EL route | [What the UI trusts](#processes-and-trust-boundary) |
| 19 | G12's journal records | **Decided** ([D3](#decisions)) **and built** (LC8): `Included` is kind 9 (120 bytes: chain, hash, block, block hash, index, status, final flag, outcome, checkpoint root; [Records](#records)), since 6 is `Account`'s, 7 `Snapshot`'s and 8 left to the approvals' `SignedTyped`; kind 2 (`Mined`) stays on the receipt's word, shown as the node's word; what is kept is decision 5's rule | One record kind more, with the storage review | [Inclusion](#inclusion-and-receipts-g12) |
| 20 | One verifier decides consensus | Follows from the user's decision 1 and the placement; listed for its cost only. Since LC9 the UI's re-checks are proved (25y), so H_lc is what is left of it | A bug in `LkdLc`, Lean's compiler or runtime, GMP or the shim reaches every green value (H_lc, H_rt) | [Placement](#placement) |
| 21 | Three departures from the reuse matrix | *Approve all three*: EthLib as a specification in `LkdProofs`, not runtime code (C4a, C4b); CompElliptic read, not ported (C4i); the Rust EL checks kept in the UI and netd beside `LkdLc.El` (D3). **Built so** (LC4a, LC4b, LC1) | Two compilations of the EL checks kept in step; the hash-to-curve maps' mathematics stays in H_vec | [What we reuse](#what-we-reuse-instead-of-writing) |
| 22 | A transaction the wallet did not send, at one of its nonces (G12) | **Decided** (the user, 2026-10-27, as recommended: [D7](#decisions)) **and built** (LC8): not named in v1. "Settled by nonce, inclusion unproved" (outcome 1) is kept only when the sender's nonce `n` is consumed at a finalized block (since LC9, D40: the sender's account at F by `AccountFinal`, accepted as final and F cross-checked agreeing, its nonce past `n`: `inclusion_keep::settled_keep`; before LC9 a `MakeSnapshot` record, whose header the UI bound to its own Keccak alone) and none of the wallet's own transactions at `n` has a receipt; it stays terminal only while no receipt is known: a newer `Mined` record reopens G12 for that hash, and a proof supersedes it. G11's alarm covers nonces `keyd` never signed. Naming it needs secp256k1 public-key recovery in `LkdLc` (reuse C11, to build) and a bisection by account proofs | G12 proves the inclusion of the wallet's own transactions only; a replacement by another holder of the key is shown as settled, not named | [Inclusion](#inclusion-and-receipts-g12) |
| 23 | G12's block and receipts from a public endpoint | **Decided** (the user, 2026-10-27: [D4](#decisions), yes) **and built** (LC7's egress v8, 10i, with its second reviewer; `06-tor.md`'s one exception): `eth_getBlockByHash(hN, true)`, its header-only form and `eth_getBlockReceipts(hN)`, by hash only, after a receipt located the block, on the transaction's `Broadcast(n)` circuit, from `g12_endpoint(tx, attempt)` (first the endpoints that took its broadcast this session, then `el_endpoint`'s pick), with EIP-2935's proof of `hN` in the same group. **D4's fallback, accepted by the user on 2026-10-27:** after a restart, G12 reads go to `endpoint_for(tx)` when the broadcast's endpoints are unknown; that endpoint learns that some wallet cares about that block. The code also falls back within a session, past the endpoints that took the broadcast, which the user also accepted on 2026-10-27 (LC9's [D59](#decisions-lc9), yes: no change) | That circuit's endpoint, which already knows the hash, learns the block (past the endpoints that took the broadcast, or in a later session, the endpoint the hash picks, on a circuit of its own, which was not given the transaction, learns that a wallet asked for that block: restated at the review, 2026-10-27); the JSON of the block and its receipts once a transaction: 3.0 to 5.5 MB on mainnet's largest measured blocks (the block 1.5 to 1.7 MB, its receipts 1.4 to 4.0 MB; [Sizes](#inclusion-and-receipts-g12)), typical blocks far less (PROBE: 63 to 850 KB of block JSON), 2.7 MB on Sepolia's largest | [Inclusion](#inclusion-and-receipts-g12) |
| 24 | The routine poll | *`finality_update` once a slot*, from one source in rotation; every source once an epoch. **Built so** (LC6's planner); LC9's live run judges a refresh's beacon `GET`s against it (D52) | About 7,200 requests and 15 MB a day over Tor (*estimate*) while `lkd` runs; a slower poll would let anchors age toward `F`. LC7 adds no periodic batch: pins are proved on demand (D21: at session start, before a review, on an explicit refresh at most once an epoch), never on a timer, so this cost stands | [Several sources](#several-sources-compared-g1-g3) |
| 25 | Where your facts persist (G19) | *`keyd`'s encrypted journal*, a `Snapshot` record kind (the user's choice, 2026-10-26). Which facts in LC7, **decided** (the user, 2026-10-27, as recommended: [D5](#decisions)): token balances (fact type 2) now, **built** (LC7: 25s's token facts, written from `MakeTokenSnapshot`, D22); ENS names as facts (type 3, query `0x0e`) deferred to the follow-up `lc9/ens-facts`; **decided in LC9** (the user's yes to D47 and D48, 2026-10-27) **and built** (lc9-ens): in place of `lc9/ens-facts`, the UI makes type-3 facts in each snapshot pass, the selected account's primary name as a reverse and a forward fact, each in a record of its own before the pass's account and token records; query `0x0e` stays reserved | One record kind more, with the storage review; the alternatives were memory only, or a file of `lkd-lc`'s with a key it would hold. Since LC9 the selected account's primary name is kept, its ENS meaning the UI's re-check alone (D47) | [The verified cache](#the-verified-cache-g19) |
| 26 | The grid for a delta's starting block (G19) | **Decided** (the user, 2026-10-27, as recommended: [D6](#decisions)) **and built** (LC7, `lkd_ui::cache::GRID`): the last committed block rounded down to a multiple of 50,000 blocks (about a week on mainnet; 32 on the development chain, so e2e sees cells close), never before deployment, so wallets that synced in the same week ask from the same block; logs fetched again are deduplicated by leaf index or by block | Up to 50,000 blocks of logs fetched again per sync | [The verified cache](#the-verified-cache-g19) |
| 27 | The suggested EL endpoints (`lkd_ctlproto::SUGGESTED`) | **Decided** (the user, 2026-10-26) **and built** (`feat/suggested-endpoints`, merged into the light client with the beacon class's share): on Sepolia ethPandaOps, 0xRPC and OnFinality (since 2026-10-29 in the order 0xRPC, ethPandaOps, OnFinality: 0xRPC builds a proof by block hash in 0.14 s where ethPandaOps takes 2.1 s, so it is asked first); on mainnet dRPC, 0xRPC and MEV Blocker. Every request netd writes, to an endpoint, a relayer, the ASP or a beacon source, carries one fixed `User-Agent`, curl's (`egress::USER_AGENT`, the same on every install), because 0xRPC answers 404 to a request without one. Over Tor, netd's own read path, 54 exits each: ethPandaOps 54 of 54 (212 ms), OnFinality 54 of 54 (341 ms), 0xRPC 54 of 54 with a `User-Agent`; on mainnet dRPC 54 of 54 (234 ms), MEV Blocker 54 of 54 (303 ms). Dropped: on Sepolia dRPC, 1RPC and publicnode; on mainnet publicnode and Flashbots Protect. Not suggested: Ambire, which refuses proofs at an explicit block on mainnet and gave 48 of 54 on Sepolia, and Tenderly, 403 over Tor | A `User-Agent` names curl, not lkd: one value every install sends, so it tells an endpoint no more than the requests do. A second reviewer: 10a and 10i restated for it | [The survey](#the-survey-2026-10-26) |
| 28 | Public beacon data directly, not through Tor | **Decided** (the user, 2026-10-26: "Beacon only, opt-in") **and built** (`lc6/beacon-direct`): `beacon_route = direct` reaches the public beacon sources over this machine's own network, through `lkd-beacon`, a process of its own that netd starts and feeds typed beacon requests, for speed and because Cloudflare refuses many Tor exits; `tor` is the default. Your own beacon node, EL reads, broadcasts, relayers, the ASP and the price reads are unaffected: Tor or your own node, as before | With it on, each public beacon source, your DNS resolver and anyone on the path see that this IP runs an lkd light client, and when; a compromised netd or `lkd-lc` could send those hosts, from your IP, data of its choice inside typed requests (a bootstrap's 32-byte root), so the light client's "nothing of yours" then rests on netd and `lkd-lc`, not on Tor. A second reviewer: egress 10i restated, `lkd-beacon`'s sandbox (26c) | [The direct route](#the-direct-route-decision-28) |
| 29 | The first checkpoint, and the light client by default | **Decided** (the user, 2026-10-28: "the light client should start by default and have its own toggle in the network page", the first checkpoint "accepted automatically when every configured beacon source (at least two) gives the same finalized checkpoint; asked in the window only when they disagree (or only one source answers)"; "on by default on public routes only", D53 kept) **and built** (`feat/lc-default`): on `node = public` with no beacon source and no `light_client = off`, `lkd start` writes the chain's suggested sources (`init::suggested_beacon`) and says so once; `light_client = off` (Networks' toggle) turns it off, sources kept. A root every configured source, at least two, named and whose bootstrap verified is written without a question, `checkpoint_from = unanimous:<n>`, and logged; any other root (`offered`: a disagreement, one source, a missing answer; or any root after a halt) is asked in the wallet through `lkd`'s control socket, `agreed:<k>/<n>` once accepted; Not now keeps it off until the toggle or the next start. This replaces step 5's comparison on the terminal (a37cf09's "confirmed by the user") for the unanimous case. Restates H_cp and invariant 25e's launcher half (25z) | **Trust on first use of the sources**: a wrong root that every configured source names (colluding sources, or a compromised netd or tor carrying their answers) becomes the trust root with no human look; its bootstrap still binds it, and the light client then follows that root's chain. The cost is the user's comparison outside the wallet, now optional (Settings shows where to compare); on own-node routes nothing changes but the toggle, which opts in with D53's notice | [The first checkpoint](#the-first-checkpoint) |

## Why, and helios

Today nothing checks Ethereum consensus. With your own node, a read is proved against that
node's own header: consistent with the node, not with the chain. With public endpoints, the
header is one endpoint's, the first that answers. A node or an endpoint can present a valid old
block, or a fork of its own making, and the Merkle proofs under it check. A sync-committee light
client closes that gap with the least the wallet can trust: one block root the user confirmed
(the checkpoint) and an honest supermajority of each period's 512-member committee.
Light-client data authenticates itself, so where it comes from matters for liveness and
privacy only.

[helios](https://github.com/a16z/helios) is the reference for a light client that verifies
what a wallet reads. lkd does not run it: its own network stack and dependencies, unverified
code deciding what is accepted, and the gaps below. The table compares helios 0.12.0
(`2af9b41`, 2026-10-05; paths in its tree) with what lkd does.

| | Guarantee | helios 0.12.0 | lkd |
|---|---|---|---|
| G1 | Anchor only on ≥ 2/3-signed headers, no forced update | `latest` is the optimistic header, which needs more than half the recent maximum participation; both maxima start at 0 after a bootstrap, so one signature moves it (`ethereum/consensus-core/src/consensus_core.rs:104-105,150-158,512-517`; `ethereum/src/consensus.rs:464`). Finalized needs 342 (`consensus_core.rs:176`). `force_update` runs only in the test runner (`tests/runner/mod.rs:51-54`) | Every proved value is at a header at least two thirds of the committee signed, and says how many. No forced update exists (25f) |
| G2 | Conflicts halt, with evidence | One source; the only equivocation check is #819's "same next committee" (`consensus_core.rs:327-335`). Two signed finalized headers at one slot go unnoticed | Two kinds of conflict halt the store when both sides carry two thirds: compared on every update whose signature verifies under a committee the store holds, across sources, against the finalized checkpoints and committees kept within `MAX_AGE`; both updates are kept (25g) |
| G3 | Several sources | One consensus RPC (`config/mod.rs:30`, `builder.rs:156-160`, `consensus.rs:55`) | Two or more per chain where they exist (open decision 2); the freshest valid answer wins |
| G4 | Catch-up while running | `advance` fetches no period update once the next committee is known, so an update two periods ahead fails on every tick until a restart (`consensus.rs:183,439-461`; the research's reading, not run) | Period updates are fetched whenever the clock or any source's claim is more than one period ahead of the store |
| G5 | An explicit, aged checkpoint, never silently replaced | A compiled-in default, slot 12704096, 388.75 days old on 2026-10-24 (`consensus.rs:162-164`, `config/networks.rs:80-82`). The 14-day age is checked only at bootstrap and by default only warns (`consensus.rs:518-526`, `builder.rs:60-61`). Any sync error switches to the plurality of checkpointz services at the highest epoch (`consensus.rs:184-204`, `config/checkpoints.rs:162-225`). A checkpoint file not exactly 32 bytes, a torn write, reverts to the default (`database.rs:45-51,56-69`) | A root the user confirmed; no default and no fallback. The age bound holds on every update, replay included. A refresh moves it only to a root the evidence reaches from it within `MAX_AGE`, printed and shown in Settings (25e, 25h; open decision 7) |
| G6 | A wrong clock alone can only delay | 12 s slots hardcoded and an unchecked subtraction (`consensus_core.rs:401-407`) in a release build without overflow checks (`Cargo.toml:140-144`). The EL timestamp is never compared with the beacon slot | Age is judged against the clock or the newest verified slot, whichever is later; "clock behind" is said; slot times follow a schedule (25i). Set back, together with keys of an old committee and netd or every source, a clock defeats the bound ([The clock](#the-clock-g6)) |
| G7 | Chain identity | The chain id comes from the configuration (`consensus.rs:124-126`); `check_rpc` is dead code (`consensus.rs:353-361`) | Signatures are checked under the pinned chain's genesis validators root; the table is injective; every answer names its chain (25d, 25o) |
| G8 | Strict forks | The fork is chosen by trial-parsing JSON; `Eth-Consensus-Version` is ignored (`types/mod.rs:51,110,164,358`) | SSZ is decoded only as the fork `Forks` gives for the attested slot, which the tag must name; bytes tagged otherwise are refused (25a, 25d) |
| G9 | Reorgs and finality labels | `BlockCache` clears on a parent mismatch (`block_cache.rs:117-151`); #858 (a hash lookup answered with a same-height replacement) open | Every fact carries its block number and hash; a reorged fact is withdrawn and said; "final" only for a fact proved at the finalized block (25k). LC9 (D38, D39): the block a shown pin or pool batch was proved at is checked again by `BlockHash` at the anchor, its hash proved from EIP-2935's slot under a later anchored header (25x); a token batch's or a name's block, and a block a transaction names, the free check only (any anchored answer at that number with another hash) |
| G10 | Every balance proved | Proved by `eth_getProof` at the resolved block (`core/src/client/node.rs:385-458`, `execution/providers/rpc.rs:253-266`), whose `latest` is the optimistic header | Every ETH balance shown or used, at every call site ([G10](#every-eth-balance-g10)) |
| G11 | Stuck and settled proved; foreign use flagged | Inclusion after `sendRawTransaction` is not tracked (`rpc.rs:380-384`) | Speed-up, cancel and "settled" follow the proved nonce beside the node's pending one; a nonce `keyd` did not sign is flagged (25m); "settled at block F, final" once the account at the finalized block, `AccountFinal`, proves the nonce past it (LC9, D40) |
| G12 | Inclusion and status proved | A receipt is checked against its block's receipts root on request (`rpc.rs:392-417`, `spec.rs:145-166`); absence is not proved | Proved through the transactions and receipts roots before the journal records it as proved (25l) |
| G14 | The code you send to is the code reviewed | `keccak(code) = codeHash` (`rpc.rs:268-279`); no pins | Code hashes pinned per chain, proved at session start, before each deposit, withdrawal, ragequit, stealth-send or registration review, and at most once an epoch on an explicit refresh; gated by risk to funds (D1): a deposit or a Privacy Pools relayed withdrawal blocked on any cause, unproved included; a Tornado relayed withdrawal on a code mismatch; ragequit, a direct withdrawal, a token send and a registration ask an acknowledgment naming the reason, never blocked; a stealth send blocked on a Multicall3 mismatch |
| G15 | Token balances proved | `eth_call` run in revm over proved state (`evm.rs:52-108`), with `validate_tx = false` (`node.rs:298-299`) | Storage proofs at keys the verifier derives itself, with the pin's storage conditions |
| G16 | Pool roots proved | Not applicable | Storage proofs of the pools' roots; the rebuilt tree must match |
| G19 | A verified cache of what the wallet uses | Nothing persists but a 32-byte checkpoint; `BlockCache` holds 256 blocks in memory (`block/block_cache.rs`) | Pool trees, withdrawal sets and stealth announcements in public caches, your facts as snapshots in `keyd`'s encrypted journal (balances, nonces, token balances, and since LC9 the selected account's primary name as ENS facts, D47); everything re-checked on load, never shown as current, final only |
| | Assurance | zkcrypto `bls12_381` 0.8.0, whose README says it "has not been reviewed or audited"; helios's extra G2 subgroup check multiplies by `Scalar::from_raw(r)`, which is 0, so it always passes (`types/bls.rs:88-93`); SSZ through `tree_hash` over a personal fork of its hashing crate (`Cargo.toml:134`); not audited (`README.md:178`); the full vectors are not in CI (`tests/sync.rs:3-27`); no fuzzing, no proofs | The Lean that runs is what the theorems are about; the vectors in CI; fuzzing through the FFI |

v1 is every guarantee above (the user's decision 3): G1 to G12 without G13, plus G14 to G16, and
G19 (the user's addition of 2026-10-26).
Where each is built, what states it, and when it lands:

| | Mechanism | Invariant | Milestone |
|---|---|---|---|
| G1 | [Validating](#validating-an-update) and [processing](#processing-an-update) an update | 25f, 25p | LC5 |
| G2 | [Conflicts](#conflicts-g2) | 25g, 25n | LC5 |
| G3 | [Several sources, compared](#several-sources-compared-g1-g3) | 25g across sources; the planner tested (`lc-public`, `lc-one-source`) | LC6 |
| G4 | [Catch-up](#catch-up) | 25f (no skipped period); liveness tested (`lc-gap`) | LC5, LC6 |
| G5 | [The checkpoint and the evidence](#the-checkpoint-and-the-evidence) | 25e, 25h, 25n | LC5, LC6 |
| G6 | [The clock](#the-clock-g6) | 25i | LC5 |
| G7 | [Forks per chain](#forks-per-chain); every answer names its chain | 25d, 25o | LC5, LC1 |
| G8 | [Validating an update](#validating-an-update), step 1 | 25a, 25d | LC3, LC5 |
| G9 | [The EL header, by hash](#the-el-header-by-hash-g7-to-g9); [LC9](#lc9-the-design-as-decided)'s `BlockHash` (D38, D39) | 25f, 25j, 25k, 25x | LC6, LC9 |
| G10 | [Every ETH balance](#every-eth-balance-g10) | 25k, 25p | LC2 (one endpoint's path), LC6 |
| G11 | [Stuck, settled and foreign nonces](#stuck-settled-and-foreign-nonces-g11); [LC9](#lc9-the-design-as-decided)'s `AccountFinal` for "settled at block F, final" (D40) | 25m, 25p | LC2, LC6, LC9 |
| G12 | [Inclusion and receipts](#inclusion-and-receipts-g12) | 25l, 25u; the journal codec row | LC8 |
| G14 | [Code-hash pins](#code-hash-pins-g14) | 25k, 25t; the gates 25w (tested) | LC7 |
| G15 | [Token balances](#token-balances-g15) | 25k, 25t; H_tok tested | LC7 |
| G16 | [Pool roots](#pool-roots-g16) | 25k, 25t; H_tree | LC7 |
| G19 | [The verified cache](#the-verified-cache-g19) | 25s, 25v; the journal codec row; 26a restated | LC6 (snapshots), LC7 (public caches, token facts), LC9 (name facts) |

The store's guarantees land in LC5 and reach the screen with LC6, whose acceptance is G1 to
G11 shown.

Later, not v1: G13 (a fee floor and band from anchored headers), G17 (stealth funds proved
address by address), G18 (balance history that adds up). Not done, with reasons:

| | Not done | Why |
|---|---|---|
| N1 | Log completeness through `logsBloom` | About 20 to 44% of mainnet blocks match a bloom query, at about 850 KB of receipts each, and the blocks fetched reveal the filter |
| N2 | A Lean EVM to run `eth_call` locally | Every `eth_call` the wallet makes has a storage proof in its place (G14 to G16) |
| N3 | `keyd` consuming reads | The configured chain id is stronger than any read, and the gap guard (7d) already blocks a lying nonce |
| N4 | FFG finality from attestations | It needs the whole validator set |
| N5 | Priority-fee percentiles | A tip is an opinion |
| N6 | Forced updates | Never |
| N7 | Proofs of pairing bilinearity or of the hash-to-curve maps' mathematics | Vectors instead, and definitional algorithms where the budget allows ([Cryptography in Lean](#cryptography-in-lean)) |
| N8 | History beyond 8191 blocks through `historical_summaries` | |
| N9 | A persisted clock floor | A clock set forward once would leave the store "too old" |

### What remains trusted

Named, so the theorems can carry them as hypotheses; the specifications themselves are reviewed
as key-handling code is.

| | Assumption |
|---|---|
| H_cp | The checkpoint: one beacon block root, written without a question when every configured beacon source (at least two) named it (since 2026-10-28, open decision 29: trust on first use of those sources), else accepted by the user, typed, or moved along verified evidence. A wrong checkpoint is a wrong chain |
| H_sc | The committees' honest supermajority: no two thirds of a committee on the chain reached from the checkpoint sign a block their fork choice did not hold as head. An honest head can still be reorged out, so a fact at a block that is not final can be withdrawn (G9); a final fact rests on finality, and two conflicting checkpoints of one epoch need FFG's safety to fail. Sync-committee messages are not slashable, through Gloas and Heze, so this is an honesty assumption, not an economic one. It covers each hand-over: a committee that signs a false next committee owns every later period |
| H_slot | An honest member signs a block root only once that block's slot has come. This is what lets verified data correct a clock that is behind |
| H_bls | BLS signatures cannot be forged (co-CDH-type assumptions) |
| H_lc | The UI only: the bytes the UI reads on `lkd-lc.sock` in reply to a query are the encoding of `lkd-lc`'s answer, for the inputs it received and the configuration the launcher gave it. **Every green value rests on H_lc.** The UI's re-check binds a value to the EL hash `lkd-lc` names: it catches faults in `lkd-lc`'s EL code, codec, compiler and runtime, never a compromised `lkd-lc`; the head cross-check (open decision 18) narrows that |
| H_rt | Lean's compiler, the clang it ships, its runtime, GMP, libuv, libc++, Lean core's `Init` and its builtins, and the shim. One verifier decides consensus; a bug there reaches the screen |
| H_vec | The mathematics the vectors check and no proof covers: that the pairing is bilinear and non-degenerate on G1 × G2; that the bench's Miller loop and fast final exponentiation compute, over the same pairs, the cube of EthLib's naive `finalExponentiation` of its `pairingCheck` accumulator (the raw Miller values differ by factors in proper subfields, which the final exponentiation removes); that `[h_eff]` lands in G2 (the order of E′(𝔽_{p²})); and G.3's `clear_cofactor`, if open decision 12 keeps it. That the hash-to-curve maps send their inputs to the curves is proved since LC4b's rest (`hashOnCurve`, with RFC 9380 E.3's isogeny identity checked by the kernel), as is the runtime's `hash_to_G2` equal to EthLib's. 25c's theorems take the rest as named hypotheses (`FinalExpCube`, `MillerLoopsCube`; `PairingCheckIs`, stated on points of G1 and G2 only, [r]P = O and [r]Q = O, since over every point of the curves no e satisfies it; `HashInG2`, that `[h_eff]` lands in G2; `LkdProofs.Lc.Bls`), never axioms |
| H_exec | The chain's execution is valid. The committee signs a block; nothing checks that its payload executes correctly |
| H_nonce | An account's nonce never decreases and rises by exactly one per value consumed. A value `n` is consumed only by an included transaction from the account at nonce `n`, by an EIP-7702 authorization the account's key signed at `n` (Prague on), or by CREATE or CREATE2 run in the account's context while it delegates to code, which needed such an authorization; each takes effect only while the account's nonce is `n` |
| H_tok | For each pinned token, while its pin's storage conditions hold (USDT: not deprecated), `balanceOf(owner)` is the value at the derived key, decoded as the pin says; reviewed per token and checked against `eth_call` offline |
| H_tree | MiMC and Poseidon are collision resistant, for pool trees (G16) |
| H_live | Some source answers. Withholding stalls the wallet visibly; it cannot mislead it |

Transport security is not among them. A beacon source may be reached in plain HTTP
([Sources, configured](#sources-configured)): whoever sits on that path (the source, a tor exit,
the network behind the exit) can alter or withhold bytes, which H_live already grants every
source, and can never have a value accepted that the checks above refuse. TLS to a beacon
source buys confidentiality of public chain data, not integrity; to an EL endpoint it is still
required (10d), since the yellow path believes what one endpoint says.

Nor is the route. On the direct route (decision 28), DNS answers and the network to the public
beacon sources are as untrusted as the sources: a forged name or a rewritten byte stalls the light
client or is refused, and adds nothing to the assumptions above. What it moves is privacy: that
the requests name nothing of yours rests, on that route, on netd and `lkd-lc` being honest, since
a compromised one could put 32 bytes of its choosing in a bootstrap's root and have `lkd-beacon`
carry them from your IP; over Tor it rests on the same two processes, but such bytes leave
through Tor.

SHA-256 and Keccak-256 are not assumptions in the same sense: a forged trie proof yields a
Keccak-256 collision the specification computes (`Spec.Mpt.binding`, proved today), and 25b
gives a forged SSZ branch the same form for SHA-256, through ssz-specs'
`verifyMerkleProof_binding`, the one result whose verifier checks node widths.

### What it does not protect against

- Withholding and censorship, and a delayed view, which is shown with its age.
- An invalid execution payload the chain itself finalizes.
- What no proof covers: the pending nonce (mempool state), fee suggestions (until G13), gas
  estimates, the completeness of logs (N1) and so of stealth announcements, relayer and ASP
  claims beyond the roots G16 anchors, whether a note is spent (a proof would name the note).
- A wrong checkpoint the user confirmed.
- Two thirds of a committee signing a false chain (H_sc). With one honest source, a false
  finalized block or next committee halts the store only when the honest chain's update for
  that period also carries two thirds, so at least 172 members signed both, at any time. That
  catches an old committee whose keys were taken after it served, when a source serves that
  period's update. A supermajority that signs only the false chain leaves the honest chain
  below 342: `lkd` refuses those updates before BLS and follows the false chain with no
  conflict. A false head that is not final is anchored, marked not final. G9's check (D39, LC9)
  withdraws what a shown pin batch or pool sync proved there once a later anchor shows another
  hash at its number (`BlockHash(N, 0)` at the first anchor at least N + 2 and again once N is
  final); a token batch's, a name's, a balance's and a nonce's values get the free check only
  (another anchored answer at N with another hash), a token staying green only while fresh. For
  an old committee, add a clock set back ([The clock](#the-clock-g6)).
- A finalized header at a later epoch that does not descend from the store's: light-client
  data carries no ancestry proof.
- A compromised `lkd-lc`, for every green value and every inclusion verdict (H_lc).
- Another holder of the key replacing a transaction at a nonce `keyd` signed: shown as settled
  by nonce, inclusion unproved.
- A contract upgraded between the anchor its pin was proved at and the block that includes the
  transaction.

## Trust per route and per attacker

**Per route.** The light client gives every route the same header; routes differ in who
serves the EL header and proofs, and in which beacon sources can be reached (open decision 9).

| Route | Header today | Header with the light client | A lying node or endpoint can still |
|---|---|---|---|
| Your node over IPC | The node's own | `lkd-lc`'s anchor; the node serves the EL header and proofs at the anchored hash. Beacon data only from public or onion sources: netd's network namespace is empty there, so a beacon node on loopback TCP is not reachable | Withhold, lag, refuse proofs at the anchor |
| Your node over loopback TCP | The node's own | The same; your beacon node over loopback TCP too, on a second Landlock port | The same |
| Your node over Tor (onion) | The node's own | The same; your beacon node as an onion service | The same |
| Public endpoints | One endpoint's, the next one's when it fails | `lkd-lc`'s anchor; any one endpoint that serves the header and a proof at that hash suffices | Withhold, all of them together; never choose the block |
| Hybrid | One public endpoint's; your node proves | `lkd-lc`'s anchor; your node proves | Your node withholds; the endpoints carry broadcasts |
| Development chain (anvil) | The node's own | Unchanged: no beacon chain | As today |

What a node or a lying endpoint can **no longer** do on mainnet and Sepolia, for a value shown
green: show an old block as the head beyond the age shown, show a fork, hide an incoming payment
beyond the age shown, show another chain, report a contract's code, a token balance or a pool root
other than the chain's, or have a transaction shown as proved mined that was not. By refusing proofs
at the anchor, or by withholding, they push values to the yellow path, where today's limits hold,
labelled. Since LC9, ENS names and prices too (D44): a refusal proved at the anchor is final and
never asked on one endpoint's word. But the reads at the anchor go to the same provers, so whoever
controls them can fail the anchored read at will (proofs the anchored root does not accept, or none)
and reach one endpoint's path, where a name is one endpoint's word again: never silently, since it
is then yellow, "(not proved at the anchor: …)", and a send to it asks `W` (D46).

**Per attacker.**

| Who | Can | Cannot |
|---|---|---|
| A compromised `netd` | Withhold or delay everything, pushing values to yellow. Hide a conflict, by dropping one source's answer: G2 and G3 hold against the sources only while netd is honest. Choose an older valid anchor (its age is shown, and bounded by `MAX_AGE`). At `--propose`, choose the root and the "n of n agree" it prints: only the user's outside comparison stands against it. Misattribute answers to sources. Feed hostile bytes to `lkd-lc`'s parsers (capped and budgeted; at worst a crash, which turns values yellow). Over TCP, reach your beacon node's whole HTTP API, as it reaches your EL node's today. See all traffic, as today. On the direct route (decision 28), have `lkd-beacon` send the public beacon hosts, from your IP, data of its choice inside typed requests (a bootstrap's 32-byte root) | Have any value shown green without two thirds of a committee signing under the configured checkpoint, and the hash and trie checks; write the evidence or the configuration; reach `keyd` |
| A compromised `lkd-lc` | Have any balance, nonce, token balance, pin result or pool root shown green; mark a nonce settled, hiding speed-up and cancel; raise or suppress the foreign-nonce alarm; give any inclusion verdict, so the UI writes a false `Included` record into `keyd`'s journal that outlives the compromise. Propose a checkpoint: an exploited `--propose`, or a `--check` reading evidence a compromised daemon wrote, prints the root the launcher writes. Roll back or erase the evidence, the conflict block included. Stop answering. Make netd fetch what egress allows; on the direct route, so carry data of its choice (a bootstrap's root) from your IP to the public beacon hosts. Since LC9 (D44): answer `Head(false)` with a header of its own making, at which the UI reads names and prices; the provers' proofs do not verify under its state root, so they take one endpoint's path, yellow, a send to such a name asking `W` (D46); with an endpoint that serves proofs under that root and is silent on the head cross-check, the anchored value, yellow, behind `W` | Reach anything but netd's typed requests; stall netd (its channel end does not block); open a file; reach `keyd`; write the configuration; have an ENS name or a price shown green that is not the chain's (LC9: green needs the head cross-check to agree, D35) |
| A compromised UI | Show anything, as today. Ask `lkd-lc` for proofs about any address (it can already ask netd). Flood `lkd-lc`, which budgets its work | Hand `lkd-lc` chain bytes: its queries are typed. Write the evidence or the configuration |
| A compromised `lkd-beacon` (the direct route) | Withhold, delay or alter beacon answers, which stalls the light client as a lying source does; learn which typed beacon requests are made, and when; connect from your IP to any host on ports 443 and 80 (any port without Landlock's network rules), and send UDP anywhere | Learn anything of yours: it receives a source's number and a typed request, never an address, a key or a frame of the UI's or `lkd-lc`'s; open a file; make a socket other than IPv4 or IPv6 (so not reach tor, netd's other sockets, `keyd` or `lkd-lc`); have anything accepted that the checks refuse |
| A lying beacon source | Stall; serve stale data, updates signed by fewer than two thirds, or garbage; claim slots it cannot back (a fetch, never a clock hint); set an update's `signature_slot`, which no one signs (it then only ranks updates); send a fork tag the table lacks (it is then faulty, never the alarm alone). Learn the poll timing and the grid | Move the anchor, or produce a conflict, without two thirds of the committee's keys (a conflict made with them halts the store only if both sides carry two thirds, with evidence); raise the unknown-fork alarm alone |
| All sources colluding, or netd | Withhold together; hide a conflict; serve an older valid view, within `MAX_AGE` and with its age shown; at `--propose`, choose the root. With two thirds of an old committee's keys and a clock set back, defeat `MAX_AGE` (G6's residual) | Move the anchor without two thirds of the store's committee's keys |
| A lying EL node | Refuse proofs (reth's default window is the tip only), pushing values to yellow; mislocate a transaction's block and index; lie about what is not anchored: pending nonce, fees, `eth_estimateGas`, log completeness, stealth announcements; hide receipts ("settled" still follows from the nonce) | Have a balance, a nonce, a token balance, a code hash, a pool root or an inclusion shown green that is not the chain's |
| The clock | Ahead: make the store too old, which asks for a new checkpoint. Behind: nothing alone, and it is said in red; with netd or every source colluding and two thirds of an old committee's keys, defeat `MAX_AGE` | Make the wallet follow a committee older than `MAX_AGE`, measured from the newest verified slot, without that collusion |
| Whoever can write the evidence file | Roll it back, tear it, erase it or the conflict block: `lkd-lc` re-verifies or re-bootstraps from the configured checkpoint | Add trust beyond `MAX_AGE` from the configured checkpoint; halt the wallet (a conflict block halts only when both its updates verify from the configured checkpoint) |
| The launcher | Unchanged: it parses no chain bytes; it writes the root it parsed from a one-shot's pipe and printed itself, once the user confirmed it | |
| `keyd` | Unchanged | |

## Architecture

### Placement

Three placements were compared: the light client in `netd`, in the UI (the a37cf09 proposal
had both), and in a process of its own. A process of its own is chosen, and netd, the UI, the
window and the launcher link no Lean runtime:

- **The UI keeps its `EPERM` filter**, so a signed transaction it holds but has not broadcast
  survives a refused call (`crates/ui/src/sandbox.rs:16-21`). Lean's runtime starts a libuv
  thread whose calls a filter must allow; whether libuv survives `EPERM` answers is not
  established.
- **netd keeps one thread and its kill filter** (`crates/netd/src/sandbox.rs:1-2`).
- **One light client per machine.** The CLI asks the daemon, so a command neither replays the
  evidence nor adds its own polling fingerprint.
- **BLS runs once.** If `lkd-lc` crashes, values turn yellow, and nothing else is lost while
  the configured checkpoint is younger than `MAX_AGE`; past it, a restart needs a refresh or a
  new checkpoint ([The age bound](#the-age-bound-max_age)).

### Processes and trust boundary

| Process | Role | Lean runtime | Sandbox |
|---|---|---|---|
| `lkd-netd` | All network I/O. Gains a `Beacon` request class, typed EL methods, a second client (the light-client channel) and re-encoding of JSON to SSZ and to RLP, untrusted | No | 19a, restated for the channel and a beacon port ([Sandboxes](#sandboxes)); one thread; its serving loop and `sys.rs` change |
| `lkd-beacon` (decision 28, opt-in) | On the direct route only: the public beacon sources over this machine's network, for netd, which starts it and forwards typed beacon requests; resolves their names itself | No | 26c: an empty file system, Landlock's TCP connects to 443 and 80, IPv4 and IPv6 sockets only |
| `lkd-lc` (new) | The store, the verifier, the fetch planner and the evidence file. Answers on `lkd-lc.sock`, peer uid checked | Yes, through `crates/lc-core` and `crates/lean-rt` | 26a: `keyd`'s order |
| `lkd-ui`, `lkd-gui`, the CLI | Clients (`crates/ui/src/lc.rs`); re-check the EL half of every answer; render | No | 19b, restated: its `connect` reaches `keyd`'s, netd's and `lkd-lc`'s sockets |
| `lkd` | Starts and supervises `lkd-lc`; holds both ends of the channel; runs the one-shots and parses the root they print; asks the user; writes the configuration. Parses no chain bytes | No | Unchanged |
| `lkd-keyd` | Unchanged in what it decides; takes no reads (N3) | `LkdBase`, `LkdCore` | Unchanged |

**What the UI trusts (H_lc), and what it checks again.** Every account or storage answer carries a
certificate of at most 64 KiB: the anchor's summary (chain id, genesis validators root, checkpoint,
slot, beacon root, EL hash, signers, finalized EL number, age), the EL header's RLP and the proof
nodes. The UI refuses an answer whose chain id is not the one `keyd`'s `GetInfo` reports; runs
`lkd-verified`'s Aeneas-refined `header::verify` and `mpt::account` / `mpt::storage` on it, as
`check_proved` does today (`crates/ui/src/wallet.rs`) but at the anchor's hash rather than one
endpoint's head; derives the storage keys of tokens, pins and pools from `lkd-verified`'s tables;
and requires every value to equal `lkd-lc`'s. A mismatch shows a red "verifier disagreement" and
leaves the value unproved. This is one specification compiled by two toolchains (`LkdLc.El` is what
the Rust is refined against), an exception to reuse D3 on purpose (open decision 21): a differential
guard against Lean's compiler, runtime, GMP, the shim and the codec, never against a compromised
`lkd-lc`, which can name the hash of a header it made over a trie it built. ENS names and prices at
the anchor (LC9, D44) are the exception: `lkd-lc` vouches for the anchored header (`Head(false)`),
which the UI re-checks (`lc_check::head`), but the ENS and price reads under its state root are the
UI's alone (`ens`, `prices`, Aeneas-refined), with no Lean read of `lkd-lc`'s beside them: one
toolchain for those values, the cost D44 states. The head cross-check (open decision 18) narrows
that: the UI asks netd for the block at each anchor number shown and shows green only when the
hashes agree. netd's own Rust reads path (`crates/netd/src/reads.rs`) stays, for good, as the
labelled fallback: the development chain, routes without a beacon source, and `lkd-lc` down, syncing
or refused.

**Labels.**

| Colour | Says | When |
|---|---|---|
| Green | "proved at block N, s of 512 signed, age" | Anchored by the light client, re-checked and cross-checked by the UI, younger than `F` (open decision 10) |
| Yellow | "proved at block N, 3 h ago" | Anchored, older than `F` |
| Yellow | "proved at block N, on <host>'s word, not anchored: <why>" (public endpoints); "proved at block N of your node, not anchored: <why>" (own-node routes) | Today's check: on mainnet and Sepolia while `lkd-lc` is down, syncing, halted, too old or refused; always on the development chain |
| Yellow | "the node's word" | Nothing proved it |
| Red | halted, clock behind, unknown fork, too old, pin mismatch, verifier disagreement | ([Failure states](#failure-states)) |

### The chain of checks

```text
 checkpoint root R (configuration, confirmed by the user)                        H_cp
   │ bootstrap: htr(header.beacon) = R; header valid at its slot's fork; current
   │            committee by its branch (86, or 2945 in Gloas); KeyValidate ×512  25e, 25c
   ▼
 store: finalized header, current and next committee; finalized checkpoints and
        committee roots kept within MAX_AGE
   │ update: SSZ of the fork Forks gives for the attested slot                     25a, 25d
   │         3·signers ≥ 2·512; attested and finalized headers valid at their own
   │         slot's fork (execution branch: 25, 2856, or 812 normalized)          25f
   │         finalized header by finality branch (169, or 735)                     25b
   │         next committee by branch (87, or 2946), or empty; no skipped period
   │         age ≤ MAX_AGE against effNow; then BLS; conflicts halt               25c, 25g, 25h, 25i
   ▼
 anchor L: the newest attested header two thirds signed (first verified wins a tie)
   │ EL hash, tagged by the header's own slot: Own (the payload's block_hash, or an
   │ upgraded header's execution_block_hash), or Parent (Gloas: the bid's parent) 25j
   ▼
 EL header RLP, fetched by that hash: keccak(rlp) = hash, a known fork's fields   14b
   │ own:    execMatches (electra-typed only); timestamp = slotTime(slot)/1000;
   │         parentBeaconBlockRoot = parent_root
   │ parent: by its own EL fork: slotNumber < slot and timestamp = slotTime(slotNumber)/1000,
   │         or a pre-Amsterdam parent before the Gloas fork                       25j
   ▼
 eth_getProof at that block's hash: account; storage under its storageRoot        14c, 14d
   ▼
 facts: balance, nonce, code hash, token balance, pool root, a block hash (EIP-2935)  25k
   │ G12: N's header by hash; transaction and receipt tries rebuilt               25l
   ▼
 lcproto answer and certificate ──► the UI: chain id, header::verify, mpt (Rust,
                                     refined), head cross-check ──► the line
```

### The Lean package

`proofs/core`, the package that requires nothing (its manifest stays empty), holds the runtime
libraries, on one toolchain (open decision 13, reuse D15):

| Library | Modules | Linked into |
|---|---|---|
| `LkdBase` (`libName "lkdbase"`) | `LkdBase.Keccak` and `LkdBase.Rlp`, moved from `LkdCore` with their namespaces kept, so no constant or statement is renamed (done, d83eb71); `LkdBase.Sha256`, ssz-specs' SHA-256 (reuse C1b; built, LC3, in namespace `Ssz.Sha256`); `LkdBase.Bytes`: the fixed-width big-endian `beBytes` and its round trip, moved from `LkdCore.Wire`, and the one little-endian helper SSZ needs, proved against `Spec.Tornado.leBytes` (D9) | `keyd`, `lkd-lc` |
| `LkdCore` | `keyd`'s core, unchanged but for importing `LkdBase` | `keyd` |
| `LkdLc` (`libName "lkdlc"`) | The light client, below | `lkd-lc` |
| `LkdLcDev` | The development fork table (its Gloas epoch the fake beacon's, or none), the minimal preset and the short bounds the e2e tests need; its one export, `lkd_lc_init_dev` (`LkdLcDev.Ffi`, LC6) | `lkd-lc` under `dev-insecure` only, which refuses to build in release |

Theorems live in `proofs/LkdProofs/Lc/*`, where Mathlib is allowed, stated over the runtime
definitions, as `Spec.CoreTrace` is over `LkdCore`'s.

| `LkdLc` module | Content |
|---|---|
| `Bytes` | `ByteArray` views read with `getD`; every offset and length read from input compared with the buffer's size before any slice |
| `Ssz.Decode`, `Ssz.Merkle`, `Ssz.Containers`, `Ssz.Frame` (built, LC3) | Typed `ByteArray` decoders and `hash_tree_root` for the light-client containers of Electra (which Fulu reuses) and Gloas, each `root` proved equal to ssz-specs' `hashTreeRoot` at its transcribed `Desc` and each decoded value proved to fit its type, the decoders' equality with `deserialize` checked by vectors only (reuse C2b, D12); normalized branches, proved equal to ssz-specs' verifier both ways; the gindex table; the `/updates` framing, proved canonical; BPO-aware digests (`ForkTable.digest`, with the mainnet and Sepolia tables until `Forks` takes them over in LC5). No light-client container is a `ProgressiveContainer`; Gloas's progressive types enter only through the gindices. Theorems in `LkdProofs.Lc.Ssz{Gindex,Branch,Frame,Merkle,Root,Decode}` |
| `Bls.Fp`, `Fp2`, `Fp6`, `Fp12`, `G1`, `G2`, `Compress`, `HashToG2`, `Pairing`, `Fav` (built, LC4a); SHA-256 from `LkdBase.Sha256` (LC3), the temporary `Bls.Sha256` removed | The bench's fast layer, in namespace `Lkd.Lc.Bls`: `Fp` on `Nat` with `Nat.powMod` at one site (`fpow`, modulus `P`); KeyValidate with Scott's test, `[r]P` as its fallback (25c); FastAggregateVerify over the sum of the participants' keys, in CoreVerify's arrangement; `clear_cofactor` as `[h_eff]P`; the final exponentiation computing the cube; the Frobenius, ψ and β constants pinned as literals, each with a kernel check (ψ and β serve only the tests' endomorphism checks against `[r]P`). The store calls `keyValidate? : ByteArray → Option G1A` once per committee key and `fastAggregateVerify (pks : Array G1A) (msg sig : ByteArray) : Bool` per update; `sigValidate?` is the signature's decompression and `[r]Q`, `fastAggregateVerifyBytes` the IRTF form over encodings. Its readable specification is EthLib's code, vendored into `LkdProofs/Vendor/EthLib/Bls` |
| `Forks` (built, LC5) | Per chain, as data, keyed on `Spec.Networks`' chain ids by a `LkdProofs` theorem (mainnet and Sepolia; anvil has none; reuse D17): genesis validators root, genesis time, fork epochs and versions, the BPO schedule, the slot-duration schedule in milliseconds (EIP-8198's form), the mainnet preset and `MAX_AGE`; the fork digests' tables LC3 kept in `Ssz.Frame` moved here |
| `Store`, `Codec` (built, LC5) | bootstrap, validate, process (no forced update), `isBetter`, conflicts and the halt, the retained checkpoints and committees, `MAX_AGE`, `effNow`, the anchor; the normalized objects and the strict-fork decoding ([as built](#the-store-and-the-evidence-as-built-lc5)) |
| `El.Rlp`, `El.Header`, `El.Mpt`, `El.Trie`, `El.Typed`, `El.History` | `Spec.Header`, `Spec.Mpt` and the runtime part of `Spec.RlpDecode` (`decodeHead`, `window`, `itemAt`, `itemsF`) moved under `LkdLc/El/`, keeping their namespaces (`Lkd.Spec.Header`, `Lkd.Spec.Mpt`), so no constant is renamed and 14b to 14d keep their statements; thin re-exports stay at the old paths. `Header` also reads fields 4 (`transactionsRoot`), 5 (`receiptsRoot`), 19 (`parentBeaconBlockRoot`) and 22 (`slotNumber`). `Trie` builds an ordered trie, proved equal to the Yellow Paper's (`Spec.Mpt.Trie`); `Typed` reads EIP-2718 transactions and receipts, a receipt's status; `History` reads a block's hash from EIP-2935's contract (LC8, [as built](#inclusion-as-built-lc8-core)) |
| `Anchor`, `Pins`, `Facts` | The EL binding; per-chain pin tables, storage conditions and storage-key derivation; account, storage, history and inclusion facts |
| `Evidence` (built, LC5), `Plan`, `Wire`, `Lc`, `Ffi` | The evidence codec and copy pick (`Evidence`); the fetch planner with its work budget, caps, order and backoff; the lcproto and channel frames, with layout and injectivity theorems (25o, 25q); `step : State → Input → State × List Effect`; the two exports |

**Runtime clean-ups**, so the moved code obeys the rules (listed in LC1):

- `decodeTree` and `decodeTreeF` stay in `LkdProofs`, never compiled: their fuel `2·|w|+1`
  grows with the input (`proofs/LkdProofs/Spec/RlpDecode.lean:19-47`). `Header` and `Mpt`
  already read through `itemsF` spans.
- `itemsF` gets a tail-recursive version with an accumulator, proved equal to it and
  registered with `@[csimp]` (`itemsAccF`, `itemsF_eq_acc`, written on `feat/light-client`;
  16,000 items walk in a 256 KiB stack).
- Everything `El` reads at run time, from LC1 on and not only G12's blocks, goes through a
  decoder over `ByteArray` offsets, whose sibling walk follows leanerSTFSpec's (reuse C7b),
  proved equal to `itemAt` and `itemsAt` in `LkdProofs`. `List UInt8` costs about 24 bytes per
  byte, and copying a `window` for each item is quadratic (`LkdLc/El/Rlp.lean:431-448`): measured
  on 2026-10-25, compiled, a list of 2,000 one-byte items takes 25 ms, 8,000 take 207 ms and
  16,000 take 1.0 s, so a hostile answer of netd's 1 MiB cap would hold the verifier for over an
  hour. RLP lists for the trie use a loop encoder proved equal to `encodeTrees` (D16).
- `Mpt.walk` stays bounded at 65 steps.
- The trie builder recurses only over key nibbles and refuses more than 65,535 items, so keys
  stay within 3 bytes and the depth is constant.

**Fast code proved equal.** `AGENTS.md` asks for `@[csimp]` with an equality proof, which must
then live inside the Init-only closure. So:

- `@[csimp]` where the proof is Init-only: ssz-specs' SHA-256 brings five, kept with their
  proofs and with `private` dropped, so `Audit.lean` can name them.
- Otherwise the runtime definition *is* the fast version, and its equality with the readable
  specification is proved in `LkdProofs` and listed in `Audit.lean` (open decision 6): the
  `ByteArray` RLP decoder, and the BLS fast layer against EthLib's readable code, whose final
  exponentiation and Miller loop equalities need Mathlib's field theory.
- `Nat.powMod` is called directly, at runtime and in proofs (`powMod_def`); lkd keeps no
  `powMod` of its own (reuse D7).
- Montgomery limbs are not used. Scott's subgroup test is, since 2026-10-29 (from leanLight): KeyValidate runs it for x ≠ 0 and falls back to `[r]P`, proved to accept exactly what `[r]P = O` accepts (25c); the committee's keys are validated with `Store.mapPar`, one task each, which runs them in place while `lkd-lc` starts no task manager.

### Runtime rules, and how they are audited

Every runtime library follows every Runtime Lean rule of `AGENTS.md`. `scripts/CheckCore.lean`
and `scripts/check-core.sh` take a list of runtime libraries, each with its allowed import
closure and its one FFI module (reuse D13; committed on `build/lc0`, `b544a67`, where
`CheckCore` moved out of `proofs/core`): the script copies the whole package into an empty
cache, builds every library's `:static` offline, and builds every library before `CheckCore`
runs; a library without a row, or a row without a library, fails.

| Library | Closure within | `@[export]` only in |
|---|---|---|
| `LkdBase` | `Init`, itself | none |
| `LkdCore` | `Init`, `LkdBase`, itself: never `LkdLc` | `LkdCore.Ffi` |
| `LkdLc` | `Init`, `LkdBase`, itself | `LkdLc.Ffi` |
| `LkdLcDev` | `Init`, `LkdBase`, `LkdLc`, itself | `LkdLcDev.Ffi` (and `LkdLc.Ffi`, which its closure holds) |

Each library is checked as `LkdCore` is today (rules 1 to 4, by module name), and every theorem
in it, `@[csimp]` equations first, must rest only on the axioms `proofs/AXIOMS.allow` lists,
whether or not `Audit.lean` lists it: `lake build` only warns on `sorry`, and a
`@[csimp]` replaces the code that runs.

What `CheckCore` cannot see is reviewed: recursion depth, and the `Init` builtins that abort
inside the runtime, whose sites in a runtime library are listed with their review notes in a
committed allowlist that `CheckCore` reads, so an unlisted new site fails, and so does a line
naming no site (`proofs/ABORTS.allow`, built in LC4a: one line `<builtin> <declaration> --
<note>` per site, a site being the declaration whose code names the builtin, a compiler-made
`f._unsafe_rec` or `f.match_1` counting as `f`, theorems and `Prop`s having none; 14 sites on
2026-10-26, `Lkd.Lc.Bls.fpow` the one `Nat.powMod`; Lean 4.35's `src/runtime/object.cpp`,
`eb6cafb`):

- `Nat.powMod` with modulus 0 is `b ^ e`, and `lean_nat_pow` aborts above an exponent of
  2³²−1 (`:1611-1636`): every modulus is a nonzero literal (reuse C5a).
- `Nat.pow` and `Nat.shiftLeft` abort on an exponent above 2³²−1, `UINT_MAX`, not only one
  beyond a machine word (`:1581-1582`, `:1612-1622`).
- An `Array` or `ByteArray` sized by a `Nat` beyond `size_t` aborts for memory (`:2602-2611`,
  `:2745-2752`).
- `ByteArray.extract` and `copySlice` convert offsets and lengths to `size_t` and abort above
  2⁶⁴−1 (`:2686-2691`).

`keyd` never depends on `lkd-lc-core`, for trust (26b): `cargo tree -p lkd-keyd` shows no such
edge, and review keeps it so; the `cargo tree` check planned for `just rust` is not built. With
one runtime crate, Cargo's `links` already rules out two runtimes in one binary.

### FFI and the runtime

One Lean runtime crate (open decision 14, reuse D14): `crates/lean-rt` (`lkd-lean-rt`,
`links = "leanrt"`) holds the only `unsafe` runtime module (`src/runtime.rs`: start once, for
the one library a process runs, whose root module initializer is a `Library`; thread enter and
exit; bytes in and out; release, through the owned handles `Object` and `Bytes`), the shim's
generic part (`shim/lkd_lean_rt.{c,h}`), and the `build.rs` that links the toolchain's `Init`,
`leanrt`, `c++`, `c++abi`, `gmp` and `uv` with `-ffile-prefix-map`, moved there from
`crates/core/build.rs`. `lkd-core` (`keyd`'s five exports, `src/abi.rs`) and `lkd-lc-core`
(five) are thin ABI crates over `lkdbase` and their own library; neither links the other's
archive. Each compiles its shim with the `leanc` and the header `lkd-lean-rt`'s build names
(`DEP_LEANRT_PREFIX`, `DEP_LEANRT_INCLUDE`) and declares the shim's functions with `Object` and
`Bytes`, so its one `unsafe` module is those calls and its `Library`. The handle is neither
`Send` nor `Sync`, as `lkd_core::Core` is.

| Symbol | Lean |
|---|---|
| `lkd_lc_init` | `initC (config : ByteArray) : Option State`: the chain id, the checkpoint, the number of sources and the generation. The preset, the threshold and `MAX_AGE` are the chain table's, never configuration |
| `lkd_lc_step` | `stepC (s : State) (input : ByteArray) : State × ByteArray`: one input in, `LkdLc.Step`'s `step` run on it (each query sent to the one handler of its kind: LC1's, LC6's, LC7's `LkdLc.Storage`, LC8's `LkdLc.Included`; a cache frame, the shell's, answered `Unsupported`), the effects out |
| `lkd_lc_reached` | `reachedC (s : State) : ByteArray`: the grid checkpoint the light client reached ([Refresh](#refresh)), empty or 44 bytes (root, slot, update count; `reachedBytes_fields`). The state is not changed: the shim hands the export a reference of its own (`lean_inc`), since Lean's export consumes its argument. `lkd-lc --check` prints it |
| `lkd_lc_propose_asks` | `proposeAsksC (input : ByteArray) : ByteArray`: the sources (1) and the slot (8) in; `Plan.proposeAsks`' `BlockRoot` requests out, 10 bytes each, as the channel carries them (`--propose`) |
| `lkd_lc_propose_agreed` | `proposeAgreedC (input : ByteArray) : ByteArray`: each source's answer in, 33 bytes (`1` and the root, or `0` and zeros); `Plan.proposeRoot`'s root and count out (33 bytes), or nothing (`--propose`; `proposeRoot_iff`) |

| Inputs, by tag | Effects, by tag |
|---|---|
| `Load(copyA, copyB, conflict, now)`: stores the bytes only | `Fetch(tag, typed request)`, `FetchPage(tag, k)` |
| `Tick(now)`: also checks the loaded evidence, at most one committee's KeyValidate or a few updates a tick, so `Status` answers in between | `Answer(conn, answer)` |
| `Fetched(tag, source, page, last, bytes)` | `Persist(copy, payload)` |
| `Failed(tag, code)` | `PersistConflict(payload)`, `ClearConflict` |
| `Query(conn, query)`, `Closed(conn)` | `Status` |

Size caps are enforced in the Rust shell before bytes enter Lean, and again per kind of request
in `Plan`. The layouts of both directions are proved injective, as `keyd`'s effects are (25o).
An input that does not decode, which the shell never writes, changes nothing and has no effect.

**LC1's core** (`LkdLc.Lc`, 25r) runs no light client, answers every query at once, as
lcproto says, and answers `Account` at one endpoint's head (decided 2026-10-28: no quorum):

- `Status`, phase Endpoint, with zero roots.
- `Account(a)` from its cache when it holds a fresh result for `a`: an answer verified at the
  current head (the anchor of the newest verified answer) younger than 12 s, or the error its
  fetch ended with, younger than 3 s, so a refused or unreachable account is told so once and
  the next ask after that fetches again. Otherwise `Pending(500)`, and the core emits
  `Fetch(tag, ProvedAccount(a))`, under a tag no fetch in flight holds, unless a fetch for `a`
  is in flight already. At most 64 fetches are in flight; past that, `Error(Busy)`. The cache
  holds at most 64 results.
- `AccountFinal` and the queries of LC7 and LC8 `Error(Unsupported)`, without a light client
  (with one, LC7's and LC8's handlers answer theirs and LC9's `accountFinalLight` answers
  `AccountFinal` at the finalized header, D40); a frame that does not decode `Error(Malformed)`.
- On `Fetched(tag, …)` for a fetch in flight: page 0, the last, of a payload that decodes as
  `ProvedAccount`'s response (the header one endpoint gave, or your node, and the proof); the
  header's own hash (`Header.keccakB`), `Header.verifyB` of the header against it and
  `Mpt.accountB` of its proof under that header's state root, else `Refused`. The answer (anchor
  kind 1, Endpoint: the header's number, its hash, 1 of 1; the account; the header and the proof
  as its certificate) or the error goes into the cache, and nothing is sent: the client's next
  ask is answered from it.
- `Failed(tag, code)` caches `Unreachable`, whatever the code, and so does a `Tick`
  for a fetch sent more than 140 s before (`Lc.fetchMs`, the planner's `jobMs`, D43; the shell's
  two phases end sooner); a `Tick` also drops results that are no longer fresh. A reply for
  a tag no fetch holds changes nothing. No connection waits on the core, so `Closed` changes
  nothing either.
- `Load` keeps the copies' bytes and moves the clock; with no light client (LC1's case, and
  every configuration without a checkpoint) it does nothing else, and the core never emits
  `Persist`, nor `FetchPage` (the response is one page). LC5's light client is below
  ([The store and the evidence, as built](#the-store-and-the-evidence-as-built-lc5)).

**The channel between `lkd-lc` and netd** (25q):

- `lkd` makes one `UnixDatagram::pair()` and keeps both ends for its whole life
  (`crates/launch/src/start.rs`, `Channel`). Each start of netd gets a duplicate of one end as
  its standard input, through `Stdio::from(OwnedFd)` (`Stdio::null()` before LC1); each start
  of `lkd-lc` gets the other end the same way. No descriptor is passed, and netd takes it
  without `unsafe` code, a duplicate of descriptor 0 when that is a Unix datagram socket
  (`crates/netd/src/lc.rs`, `inherited`); any other standard input is no channel.
- A datagram arrives whole or not at all, so a netd killed mid-reply leaves no partial frame.
- Pages are pulled: each `Fetch` or `FetchPage(tag, k)` gets exactly one reply of at most
  60 KiB. A response of one page is complete in its first reply, and netd holds nothing of it
  for paging (it keeps the reads by block hash, below);
  a longer one, at most 8 MiB (a block body, its receipts, a large beacon object), is held by its
  (generation, tag) until its last page is pulled, at most 4 of them and 24 MiB together, one
  more evicting the least recently paged (D12, `crates/netd/src/lc.rs`), so that a pin or token
  batch of one-page replies evicts no body mid-paging. A fetch under a (generation, tag) held
  drops what it held; a `FetchPage` for a response never held, evicted or pulled to its end, or
  past its last page, is `NoPage`.
- Both ends are non-blocking: netd sets its end so before its sandbox (`set_nonblocking`) and
  drops a reply on `EAGAIN`, which `lkd-lc` times out; `lkd-lc` treats `EAGAIN` as `Failed`. A
  stopped or compromised `lkd-lc` cannot stall netd.
- Every datagram carries (generation, tag); the generation comes from `lkd-lc`'s argument
  vector, and a restarted `lkd-lc` drops stale replies by it.
- G12's requests carry the transaction's hash, and netd derives their isolation group as for a
  `Receipt`: the known broadcast's `n`, else a fresh one.
- The layouts are `LkdLc.Wire.Channel` and `lkd_verified::lc_channel`, refined, with a Kani
  harness; netd decodes before egress, and answers a non-canonical datagram `Failed`, changing
  nothing.
- netd's filter already allows `recvfrom`, `sendto` and `ppoll`
  (`crates/netd/src/sandbox.rs:71-98`); its loop needs a multi-descriptor `ppoll` wrapper in
  `crates/netd/src/sys.rs`, a module allowed `unsafe`, with its second reviewer (`wait`, and
  `socket_type`, the `SO_TYPE` read that tells the channel from a terminal or `/dev/null`).

**netd's loop (M).** It `ppoll`s its listener, its open UI connections (at most 16) and the
channel, and serves one request at a time, by rounds (`crates/netd/src/server.rs`, `turn`; D43):
after serving a datagram it notes the UI connections with a frame waiting then and serves one
frame of each in turn, then the next waiting datagram, then a new round; a datagram that arrives
while netd is idle waits only for the frames already waiting, one per connection; with no
datagram waiting, frames as they come, the connections taking turns. So a datagram waits at most
one round, and a UI frame at most one datagram, however fast the other side's requests come.
Right before it serves a decoded `Fetch`, netd sends `Started` (`0x83`) under the fetch's
generation and tag, dropped as any reply when sending it would block; never for a `FetchPage`,
answered at once from what netd holds, or for a datagram that does not decode. Every
light-client request has a total deadline covering SOCKS, TLS and the body
(`crates/netd/src/lc.rs`, `lkd_verified::deadlines::service_ms`): 8 s for a beacon request
(`BEACON_MS`), 27 s for G12's block and its receipts (`BODY_MS`: ⌈4/3 · 19.80 s⌉, PROBE's p95 of
the largest body over Tor, [As built, lc8-prep](#lc8-prep)), 12 s for any other request to the
EL route (`EL_MS`: what `ProvedAccount` gathers, an `ElHeader`, an `ElProof`, an `ElStorage`),
enforced by setting each read and write timeout to the time remaining
(`crates/netd/src/deadline.rs`); one that misses it, on a cold onion or `Light(src)` circuit too,
is answered `Failed(Unreachable)`, never `TimedOut`, which only `lkd-lc`'s shell writes, and
`lkd-lc` backs off. The UI's 40 s (`crates/ui/src/netd.rs`, `TIMEOUT`,
`deadlines::UI_NETD_TIMEOUT_MS`) is a budget: one 10 s wait at the node (`UI_FRAME_MS`, one
read's), plus a body's 27 s, plus 3 s (`MARGIN_MS`). It bounds no UI frame's wait: netd gives
UI frames no total deadline, a frame that reads several times (a name's `ProvedNameAt`, its
parts in turn: 27.1 s measured, lc9-deadlines' case (c)) holds netd for as many waits, and a
round serves a frame of each UI connection waiting; a frame past it fails or falls back and is
asked again (tested, not proved). Whether tor finishes a rendezvous after the stream is
abandoned is measured in e2e.

**`lkd-lc`'s shell** (`crates/lc`, built in LC1). One Rust thread runs a `ppoll` loop over the
listener, at most 8 client connections, the channel and a one-second tick; Lean's runtime adds
its libuv thread. Only `lkd-lc` asks netd for light-client data, and no chain bytes from the UI
reach it. The shell decides nothing; it feeds the core one input at a time, carries out its
effects in order, and enforces the caps the core relies on before bytes enter Lean. What it
answers itself, the public caches' frames, it answers from their file, which the core never
holds (G19, D8):

- **Clients** (`shell.rs`): the listener is `lkd-lc.sock`, `0600`, accepted non-blocking
  (`accept4` with `SOCK_NONBLOCK`), a connection from another uid closed unread
  (`SO_PEERCRED`); past 8 connections the listener is not waited on. A frame is read into a
  buffer of at most 4 + 65,536 bytes and handed whole, length included, as `Query(conn, frame)`;
  a length of 0 or above 65,536 is handed as its 4 bytes alone, which the core answers
  `Malformed`, and the connection is closed once that answer is written. A connection whose
  answer is not yet written is not read, so a client that writes without reading holds one answer
  in `lkd-lc`; one with nothing to read or write for 10 s is closed. Each closed connection is
  told as `Closed(conn)`.
- **The public caches** (`shell.rs`, `cache.rs`; G19, D9): a whole client frame tagged `0x0a` to
  `0x0c` (`CacheRead`, `CacheAppend`, `CacheCommit`) never reaches the core. The shell decodes it
  (`lc_wire::decode_query`) and answers it at once, on its connection, from the caches' file
  (`Cache::answer`): `CacheChunk`, the committed items from its start, as many whole items as one
  answer holds (65,413 bytes); `CacheStored`; or `Error` `Malformed` (not exactly a cache
  frame's encoding; items not whole), `Unsupported` (no caches' file; no such region), `Refused`
  (the offset, count, capacity or order) or `Busy` (another live connection's transfer). Each
  answer names the identity of the core's `Status` answer, asked once at start on a connection
  id no client gets. A connection closed for any reason (its end, an error, a length out of
  bounds, 10 s idle) has what it staged and did not commit dropped (`Cache::discard`) before the
  core is told `Closed`.
- **The channel** (`channel.rs`): a `Fetch` is written as generation ‖ tag ‖ request, a
  `FetchPage` as generation ‖ tag ‖ `01` ‖ page; a datagram that cannot be sent (`EAGAIN`, or no
  channel on standard input) is told to the core at once as `Failed(tag, NotSent)`. A fetch is
  waited for in two phases (`shell::Flights`, D43, with `lkd_verified::deadlines`' constants):
  sent and not started, until `QUEUE_LIMIT_MS` (120 s) after its sending; from its first
  `Started` (of this generation, for a tag in flight not yet started), netd's deadline for its
  kind and `MARGIN_MS` (3 s): 11 s for a beacon fetch, 15 s for an EL fetch (`ProvedAccount`,
  `ElProof`, `ElHeader`, `ElStorage`), 30 s for a block body (`ElBlock`, `ElReceipts`); a
  `FetchPage`, answered at once from what netd holds, 123 s from its sending. Past it the core
  is told `Failed(tag, TimedOut)`, and standard error says which kind timed out and whether
  netd had started it (`shell::timed_out_line`). A fetch is sent only while fewer than two of
  the shell's fetches are queued in netd (sent and not started, awaited or timed out: one timed
  out unstarted counts until its page or failure, its `Started` not ending the count since netd
  then serves it, or until 240 s after its sending or its kind's service and 3 s after that
  `Started`, whichever is later), else the core
  is told `Failed(tag, NotSent)` at once; pages are neither counted nor refused. So at most one
  of its datagrams is ahead of a fetch, and a fetch waits before its `Started` for at most the
  rest of a round, one service and one more round ([The deadline model
  (D43)](#the-deadline-model-d43)). A `Started` never reaches the core. Each phase ends below
  the core's backstops, `Plan.jobMs` (140 s, and LC1's `Lc.fetchMs`) and `Plan.bodyJobMs`
  (155 s), which count a paged fetch from its last page (`Refinement.Deadlines`). The one-shot
  `--propose` waits for each `BlockRoot` in the same two phases, within its 60 s.
  A reply is handed in only for a tag in flight and of this `lkd-lc`'s generation, at most 64 a
  turn: a late reply, one for a fetch timed out, or one netd answers a predecessor, is dropped.
  `lc_channel::decode_reply` bounds the page (61,421 bytes) and the code (1 to 12).
- **The evidence** (`evidence.rs`, [The evidence file](#the-evidence-file)): read at start and
  handed as `Load`, each copy within 16 MiB; `Persist` written in place, a write that fails said
  on standard error and nothing else.
- **`lkd-lc`'s arguments**: `--chain-id`, `--generation`, `--evidence <home>/lc`, `--ready-fd 1`,
  `--verbose`, and in LC1 no checkpoint and no beacon source (`--checkpoint` and `--sources`
  exist, zero by default; with both, LC6's light client runs). A `dev-insecure` build also takes
  `--dev-genesis`, `--dev-gvr` and `--dev-gloas`, the fake beacon's chain ([as
  built](#the-planner-and-anchored-reads-as-built-lc6)). A `dev-insecure` build also takes `--tamper-certificates`, which
  alters every `Account` answer's proof (the e2e test of the UI's re-check); it refuses to build
  in release, and `release-check.sh` checks no release binary names it.

**lcproto**, the UI's protocol with `lkd-lc` (25o). Queries are typed: `Status`, `Account(a)`,
`AccountFinal(a)` (at the finalized EL block), `Token(i, owner)`, `Pin(i)`, `Pool(i)`,
`Included(h, block hint, index hint)`. A query is answered at once: from cache, proved, with
its anchor's summary and age, or `Pending(retry_after)`, and the UI asks again; the UI's and
the CLI's read timeout on `lkd-lc.sock` is 2 s. The client (`crates/ui/src/lc.rs`,
`Lc::account_within`) asks again after each `Pending`, after the pause it names (kept within
50 ms and 5 s), and at once after an answer that did not come within the 2 s, until another
answer comes or a bound passes (`ANSWER_WITHIN`, 62 s, for the overview's differential: a
budget since D43, the UI giving up before `lkd-lc` does, whose shell waits up to 120 s for netd
to start a fetch and whose core ends a read at 140 s). The planner serves user
queries first, newest first (account reads, and the EL headers they, LC7's storage reads and
G12's job want), then the
bootstrap and catch-up, then LC7's storage reads (pins, tokens, pools) and G12's job, then polls;
a poll is skipped, not queued, while an account or a storage read waits, never for G12's job,
and G12's block bodies are sent only while none waits, beside at most one storage fetch; at most
two fetches are in flight, two new ones an input (D43: netd is serial, so more would only queue
there, outside these priorities).
An automatic overview refresh asks one account proof per address shown and nothing else. The
Rust codec is `lkd_verified::lc_wire`, refined against `LkdLc.Wire`.

### Frame layouts

Three directions, each a set of typed messages with one layout per message: lcproto between the
clients and `lkd-lc`, the channel between `lkd-lc` and netd, and `lkd_lc_step`'s inputs and
effects between `lkd-lc`'s shell and `LkdLc`. Common rules, as in `keyd`'s wire format
([`01-keyd.md`](01-keyd.md#wire-format)):

- Integers are unsigned, big-endian, of the width the tables give; addresses are 20 bytes,
  hashes and roots 32. There is no RLP and no SSZ at these boundaries; RLP and SSZ bytes travel
  inside, as byte strings, and are checked where they are read.
- A byte string has a length before it (4 bytes unless the table says otherwise), except the
  last field of a frame, a datagram or an input, which runs to its end ("the rest").
- A tag or kind byte comes first and fixes the layout; every value a table does not define,
  tags, kinds, phases and codes alike, is reserved and refused, so a later milestone defines it
  without changing a layout LC1 accepts.
- Decoding reads every field where encoding writes it, refuses bytes too short to hold them, an
  unknown tag or a reserved value, and accepts what it read only when encoding it gives back
  exactly the bytes it was given. Decoding is total, and every accepted frame, datagram or
  input has one meaning and one encoding (25o, 25q).

The definitions are `LkdLc.Wire` (namespaces `Lkd.Lc.Wire`, `.Channel` and `.Step`); the Rust
codecs `lkd_verified::lc_wire` and `lkd_verified::lc_channel` are refined against them. The
inputs and effects have no Rust codec in `lkd-verified`: `crates/lc-core` writes the inputs and
reads the effects, with Kani harnesses, as `lkd_core::effects` does for `keyd`.

**lcproto.** A frame is a 4-byte body length `L`, 1 ≤ `L` ≤ `MAX_BODY` = 65536 (64 KiB, as
netd's), then `L` body bytes: a tag, then its fields. Queries have tags below `0x80`, answers
`0x80` and above.

| Tag | Query | Fields after the tag | Body |
|---|---|---|---|
| `0x01` | `Status` | none | 1 |
| `0x02` | `Account(a)` | address (20) | 21 |
| `0x03` | `AccountFinal(a)` | address (20) | 21 |
| `0x04` | `Token(i, owner)` | token index (2), owner (20) | 23 |
| `0x05` | `Pin(i)` | pin index (2) | 3 |
| `0x06` | `Pool(i)` | pool index (2) | 3 |
| `0x07` | `Included(h, block hint, index hint)` | transaction hash (32), block number (8), transaction index (4) | 45 |
| `0x08` | `CheckSnapshot(record)` | the record (the rest, at most 65,535 bytes) | 1 + r |
| `0x09` | `MakeSnapshot(a)` | address (20) | 21 |
| `0x0a` | `CacheRead(cache, first)` | cache (2: kind, index), first item (4) | 7 |
| `0x0b` | `CacheAppend(cache, offset, items)` | cache (2), offset (4), items (the rest, 1 to 65,529 bytes) | 7 + n |
| `0x0c` | `CacheCommit(cache, count, block, root)` | cache (2), count (4), block (8), root (32) | 47 |
| `0x0d` | `MakeTokenSnapshot(owner)` | owner (20) | 21 |
| `0x0f` | `BlockHash(n, final)` | block number (8), final (1: `0` or `1`) | 10 |
| `0x10` | `Head(final)` | final (1: `0` or `1`) | 2 |

`0x0e` stays reserved for D5's `MakeNameSnapshot` (unused: D47), `0x11` to `0x7f` for later
queries. `BlockHash(n, final)` asks for EL block n's hash proved at P, the anchor's attested
header (`final` 0) or the finalized one (`final` 1): G9's reorg check (D38); `Head(final)` asks for
P's EL header (D41). An index is
the entry's place in the chain's table (`LkdLc.Pins`' `tokens`, `pins` and `pools`, which
`lkd_verified::pins` transcribes). LC1's `lkd-lc` answers `Status` and `Account`, and
`Error(Unsupported)` to the other six until their milestones. The cache frames (`0x0a` to
`0x0c`, G19, D9) are `lkd-lc`'s shell's, which answers them before they reach the core; the core
answers a cache frame `Error(Unsupported)`. `MakeTokenSnapshot(owner)` asks for a snapshot record
of `owner`'s account and of every pinned token's balance for it at the finalized EL block (D22),
answered `TokenRecord`. The core reads a `CheckSnapshot` or `CacheAppend` frame, up to 64 KiB, as
a `ByteArray` (`decodeQueryB`), and every other query, at most 51 bytes, as a list.
`CheckSnapshot`'s record is a `Snapshot` journal record's content as the UI read it after unlock
([the verified cache](#the-verified-cache-g19)), which lcproto carries undecoded and `lkd-lc`
decodes ([snapshot records](#snapshot-records), below). A frame holds at most 65,535 bytes of
record, and so does a record: **decided (G19, as built): a set of facts larger than one frame is
split into self-contained records of at most one frame each, each with its own update and
header**, not asked in parts, so every record is checked alone. `MakeSnapshot(a)` asks `lkd-lc` for
the record of the account at `a` at the finalized EL block, which the UI writes to `keyd`'s journal.

Every answer starts with the identity, 72 bytes: the chain id (8), the genesis validators root
(32) and the checkpoint root (32). Both roots are zero while `lkd-lc` runs no light client,
which is LC1's case: a client tells a light-client answer from one endpoint's by the anchor's
kind, never by the roots alone.

| Tag | Answer | Fields after the tag | Body |
|---|---|---|---|
| `0x81` | `Status` | identity (72), phase (1) | 74 |
| `0x82` | `Account`, anchor kind 1 | identity (72), anchor (45), address (20), nonce (8), balance (16), storage root (32), code hash (32), header length (4), header, proof length (4), proof | 234 + H + P |
| `0x82` | `Account`, anchor kind 2 | identity (72), anchor (45), the anchored fields (58), then as kind 1: address (20) to proof | 292 + H + P |
| `0x83` | `Pending(retry_after)` | identity (72), retry after, in milliseconds (4) | 77 |
| `0x84` | `Error(code)` | identity (72), code (1) | 74 |
| `0x85` | `Token` | identity (72), anchor (103), token index (2), owner (20), contract (20), pin (1), detail (1), header length (4), header, account length (4), nodes, k (1: 1 to 8), k × (value (32), length (4), nodes) | 229 + H + A + Σ(36 + Sⱼ) |
| `0x86` | `Pin` | identity, anchor, pin index (2), verdict (1), detail (1), contract (20), code hash (32), implementation (20), implementation's code hash (32), header length (4), header, account length (4), nodes, k (1: 0 to 8), k × (value (32), length (4), nodes), implementation-account length (4), nodes | 284 + C, C = 13 + H + A + Σ(36 + Sⱼ) + I |
| `0x87` | `Pool` | identity, anchor, pool index (2), w (1: 1 to 8), w × word (32), header length (4), header, account length (4), nodes, w × (length (4), nodes) | 179 + 32w + C, C = 8 + H + A + Σ(4 + Sⱼ) |
| `0x88` | `Included` | identity, anchor, tx hash (32), block number (8), block hash (32), verdict (1), index (4), success (1), refusal (1), proving header length (4), header, N's header length (4), header, history-account length (4), nodes, history-slot length (4), nodes | 255 + C, C = 16 + P + Hₙ + A + S |
| `0x89` | `Snapshot(facts)` | identity (72), the facts' verdicts (the rest, at least one byte: one per fact of the record, in its order) | 73 + n |
| `0x8a` | `Record(r)` | identity (72), a snapshot record (the rest, at least one byte) | 73 + r |
| `0x8b` | `CacheChunk` | identity, cache (2), committed count (4), block (8), root (32), first item (4), items (the rest) | 123 + n |
| `0x8c` | `CacheStored` | identity, cache (2), staged (4), committed (4), block (8) | 91 |
| `0x8d` | `TokenRecord` | identity, a snapshot record (the rest, at least one byte) | 73 + r |
| `0x8e` | `BlockHash` | identity (72), anchor (103), block number (8), status (1), block hash (32), proving header length (4), header, history-account length (4), nodes, history-slot length (4), nodes | 229 + P + A + S |
| `0x8f` | `Head` | identity (72), anchor (103), header length (4), header | 180 + H |

`0x90` and above are reserved for later answers. `Account` answers both `Account` and
`AccountFinal`; its anchor says which block. The account fields are `mpt::account`'s, in its
widths (a balance above 2¹²⁸ is refused there already). The certificate is the EL header's RLP
(H bytes) and the proof's nodes one after the other (P bytes), as `mpt::account` reads them;
the body's cap bounds H + P, and a proof netd forwarded always fits (below).

| Anchor field | Width | Kind 1 (LC1) | Kind 2 (LC6) |
|---|---|---|---|
| kind | 1 | `1`, Endpoint: one endpoint's head (or your node's), count 1 of 1 (it was Agreed, a quorum's, until 2026-10-28) | `2`, Anchored: the light client's anchor names the block's hash; the anchored fields follow these 45 bytes |
| block number | 8 | The header's number | The EL block's number, its header's |
| block hash | 32 | The header's own Keccak-256, which `header::verify` binds it to | The EL hash the beacon header below names (25j), which `header::verify` binds the header to |
| count | 2 | `1` | How many of the committee signed that beacon header |
| of | 2 | `1` | The committee's size |

| Anchored field | Width | Value |
|---|---|---|
| slot | 8 | The beacon header's slot: the anchor's attested header, or for an `AccountFinal` answer the finalized header |
| beacon root | 32 | That beacon header's `hash_tree_root` |
| finalized | 8 | The finalized EL block's number, at that anchor |
| age | 8 | Milliseconds from `slotTime(slot)` to `lkd-lc`'s clock when it answered, `0` when the clock is behind |
| final | 1 | `1`: the block is the finalized EL block, asked at its hash (`AccountFinal`); `0`: the anchor's |
| EL tag | 1 | `0` Own: the hash is that beacon block's own payload's; `1` Parent: its parent payload's, from `GLOAS_FORK_EPOCH` on (25j) |

`final` and the EL tag take `0` or `1`, any other value refused. The certificate of an anchored
answer comes from netd's `ElHeader` and `ElProof` responses (below): at most 2,048 bytes of
header and one page of proof, so 292 + 2,048 + 61,333 ≤ 65,536 and the answer always fits.

**LC7's and LC8's answers** (`Wire.TokenAnswer` to `Wire.CacheStored`). `Token`, `Pin`, `Pool`
and `Included` are anchored by kind 2, as an anchored `Account` is: 103 bytes, the 45 then the 58
anchored fields, `final` 1 when the answer is at the finalized header; `Included`'s anchor names
the proving block. Their certificates are fields, never optional (D15): a storage certificate is
the EL header's RLP (H, 1 to 2,048 bytes), the contract's account proof (A) and, per key in its
key set's order, the value read and the slot's proof (Sⱼ); `Pool`'s carries one slot proof per
word; `Included`'s is the proving header (P), N's header (Hₙ) and EIP-2935's account and slot
proofs (A, S). Every other value is refused (each answer's `ok`, 25o):

- `Token`: pin `0` matched, `1` upgraded, `2` mismatch, `3` condition failed (never `4`: the
  implementation's code is not read); detail the failed condition's place, 1 to 8, when the pin
  is `3`, else `0`; 1 to 8 keys, the balance's then the pin's slots (`Pins.tokenSlots`).
- `Pin`: verdict `0` to `4`, `4` the pinned implementation's code mismatching; detail as
  `Token`'s; 0 to 8 keys (`Pins.pinSlots`); the implementation's code hash zero exactly when its
  account proof is empty.
- `Pool`: 1 to 8 words, the layout's head words then the root word when `Pins.rootSlot` of the
  head value is defined, and one slot proof per word, in their order.
- `Included`: verdict `0` proved, `1` ahead, `2` too old, `3` too large, `4` refused; the block
  hash nonzero exactly for `0` and `3`; index and success zero unless `0`; refusal 1 to 8 exactly
  for `4`, numbered as `Inclusion.Refusal`'s constructors (`1` hash proof, `2` header, `3` body,
  `4` not in the block, `5` transaction, `6` receipt, `7` transactions root, `8` receipts root),
  else `0`; both headers (1 to 2,048 bytes each) exactly for `0` and `3`, else empty; EIP-2935's
  proofs exactly for `0` and `3` when N is not the proving block's number, else empty.
- `CacheChunk`: whole items of the region's size, by the cache's kind (its high byte: `1` tree
  leaves 32, `2` Tornado spent sets 40, `3` PP deposits 140, `4` PP ragequits 108, `5` ASP leaves
  32, `6` announcements 111, `7` PP withdrawals 88; other kinds refused), none when the first item
  is the committed count, the root zero for a set (every kind but `1` and `5`). `CacheStored`:
  staged at or past committed. `TokenRecord`: a snapshot record of at least one byte, which the
  record codec reads (25s).

**LC9's answers** (`Wire.BlockHashAnswer`, `Wire.HeadAnswer`). `BlockHash` and `Head` are
anchored by kind 2 at the header P they name, the anchor's attested header (`final` 0) or the
finalized one (`final` 1), `final` as asked. Their certificates are fields, an absent part empty
(`Wire.BlockHashCert`): `BlockHash`'s is P's header (P, 1 to 2,048 bytes) and EIP-2935's account
and slot proofs at P (A, S); `Head`'s is P's header (H, 1 to 2,048 bytes). Every other value is
refused (`BlockHashAnswer.ok`, `HeadAnswer.ok`, 25o):

- `BlockHash`: status `0` proved, `1` ahead (n past P's number), `2` too old (P's number past
  n + 8191); the hash nonzero and P's header present exactly for `0`; EIP-2935's proofs exactly
  for `0` when n is not P's number (P's own hash needs no proof), else empty. That the status
  is n's against P is the handler's (`Blocks.blockHashLight`), and the UI checks the certificate
  again (`lc_check::history_hash`).
- `Head`: P's header, 1 to 2,048 bytes.

What depends on the chain's table is not the decoder's to check: that `Token`'s keys are its
pin's slots after the balance's, that `Pin`'s implementation is zero exactly when the pin has no
proxy and its code present exactly for the pinned implementation, that `Pool`'s words follow its
layout. The handlers prove it of what they answer (25t), and the UI checks every certificate
again (D15).

`Snapshot` answers `CheckSnapshot`: one verdict byte per fact of the record, in its order,
`0` not held (its proof fails under the header the snapshot's update finalizes), `1` held,
`2` too old (the snapshot's block is beyond the evidence's reach, `MAX_AGE` from the
configured checkpoint, so nothing in it is proved); `3` to `255` are refused. As built
(`Lc.checkSnapshot`, `Lc.checkRecord`):

- `Error(Unsupported)` without a light client; `Pending` while it has no store or checks its
  evidence; `Error(NotAnchored)` when its store is halted or older than `MAX_AGE`;
- `Error(Refused)` when the bytes are not a record, name another chain, or hold an update that
  does not decode as its fork and kind or does not verify (`Store.verifyHistorical`: `formOk`, a
  finality branch to a header other than genesis, the signature under the committee the store
  holds for its signature period, current, next or past);
- every fact `2`, too old, when the update's signature period is before the store's and the
  store holds no committee for it (the configured checkpoint's period is the oldest a store ever
  holds, so this is "beyond the evidence's reach");
- `Pending` when the update's signature period is after the store's and the store holds no
  committee for it (`Lc.ahead`): the store has not reached that period, so nothing is judged yet,
  and the client asks again as it catches up. A store started from a refreshed checkpoint holds
  that checkpoint's committee alone until its catch-up ([Refresh](#refresh)), so a snapshot written
  before the restart is often ahead of it. These two are the only cases with no committee for the
  update's period (the store always holds its own period's): an update that fails under a
  committee the store holds is refused, never `Pending` (`checkRecord_pending`,
  `checkSnapshot_pending`, 25s);
- every fact `0` when the EL header is not the block the update's finalized header names
  (`Anchor.bind`, 25j, by that header's own slot's tag), or the record's block, time or tag are
  not that header's;
- otherwise each fact `1` exactly when `Spec.Mpt.accountB` reads, from its proof under that
  header's state root, exactly the fact's account, `0` otherwise.

`Record` answers `MakeSnapshot(a)` (`Lc.makeSnapshot`): `Error(Unsupported)` without a light
client; `Error(NotAnchored)` unless the phase is Anchored and the evidence's latest update is a
finality update (or an update) whose finalized header is the store's (`Lc.finalizer`); the record
once the planner holds the EL header at that header's EL hash, bound (25j), and `a`'s proof there
(25k), both checked again (`Lc.snapshotRecord`): one fact, at that block, with that update; the
read's error while it is told; otherwise `Pending`, the read wanted at the finalized header's EL
hash (`Plan.want`, which drops the reads at other hashes: reads are per anchor, and the next
`Account` asks at the anchor again). The planner reads at the finalized header as at the anchor:
`ctxOf` names both.

#### Snapshot records

`LkdLc.Wire.Snapshot` and `lkd_verified::snapshot`, refined (25s): what `keyd`'s journal keeps as a
`Snapshot` record (kind 7), what `Record` carries and `CheckSnapshot` checks. One finalized EL
block's facts, with what proves them again; at most 65,535 bytes, the whole record.

| Offset | Width | Field |
|---|---|---|
| 0 | 1 | kind, `7` (the journal's `Snapshot`) |
| 1 | 8 | chain id |
| 9 | 8 | the EL block's number `N` |
| 17 | 8 | its header's timestamp, in seconds (what the UI shows the age from) |
| 25 | 1 | EL tag: `0` Own, the finalized beacon header's own payload's hash; `1` Parent, its parent payload's (25j) |
| 26 | 1 | the update's fork: `0` Electra, `1` Fulu, `2` Gloas, as the evidence numbers them |
| 27 | 1 | the update's kind: `0` an update, `1` a finality update (`2`, optimistic, finalizes nothing: refused) |
| 28 | 4 | the update's length `U`, at least 1, then its SSZ: the update that finalized the beacon header naming `N` |
| 32 + U | 4 | the EL header's length `H`, at least 1, then its RLP |
| 36 + U + H | 2 | the number of facts `n`, at least 1, then the facts: the account facts, then the token facts, then the name facts |

An account fact is its type (1: `1`), the address (20), the account's nonce (8), balance (16),
storage root (32) and code hash (32), the proof's length (4) and its nodes one after the other:
113 + P bytes. A **token fact** (LC7, fact type 2) is its type (1: `2`), the token's index in
its chain's table (2, `LkdLc.Pins.tokens`, `lkd_verified::tokens`' order), the owner (20), the
token's contract (20), the contract's account (88: nonce 8, balance 16, storage root 32, code
hash 32), the proof's length (4) and its nodes, then the slot count k (1: 1 to 8) and k slots,
each a value (32, a word) and its storage proof's length (4) and nodes: 136 + P + Σ(36 + Sⱼ)
bytes. A **name fact** (LC9, fact type 3, D47) is its type (1: `3`), its direction (1: `0` an ENS
name's forward read, `1` an address's reverse read), the subject's length (1: 1 to 255) and the
subject (the normalized name, or the 20-byte address), the part count (1: 5 forward, 3 reverse,
in `ens::Bundle`'s and `ens::ReverseBundle`'s order), then each part: the contract (20), its
account (88), the proof's length (4) and its nodes, the key count (1: 0 to 10) and each key,
the key (32), its value (32) and its storage proof's length (4) and nodes; a part the read did not
need is all zero, with no nodes and no key: 4 + L + Σ(113 + Pᵢ + Σ(68 + Kᵢⱼ)) bytes. The account
facts come first, then the token facts, then the name facts, and the count counts all three; a
lower type after a higher one is refused, and so are types `0` and `4` to `255`. A
record is 38 + U + H bytes plus its facts'. Decoding reads every field where encoding writes it
and keeps what it read only when encoding it gives back exactly the bytes, so a record has one
meaning and one encoding; `lkd-lc` reads it as a `ByteArray` (`decodeRecordB`, a loop over the
account facts while the next byte is their type, then one over the token facts and one over a
token fact's slots, then, LC9, one over the name facts, their parts and their keys).

**The held rule** (`LkdLc.Lc.tokenHeld`, 25s): `CheckSnapshot` answers one verdict a fact, the
account facts' first. An account fact is held when `Spec.Mpt.accountB` reads exactly its account
from its proof under the bound header's state root. A token fact is held exactly when its index
names a token of the configured chain's table whose pin's contract is the fact's contract;
`accountB` reads exactly the fact's account under that state root, with the pin's code hash;
the fact holds one slot for each key a token read asks (`Pins.tokenSlots`: the owner's balance,
then the pin's proxy and condition slots), each value the one `Spec.Mpt.storageB` reads from the
slot's proof under the account's storage root; and the pin's verdict over that code hash and its
slots' values, the implementation's code not read, is matched (`LkdProofs.Lc.SnapshotToken`,
`tokenHeld_iff`). The implementation's code hash is not in the record: the session's pin set
holds it (D21, EIP-6780). The owner's balance is the first slot's value, masked by the token's
mask (`Pins.balance`, USDC's bit 255 its frozen flag, D17). A name fact (LC9) is held exactly
when every nonempty part's account is what `Spec.Mpt.accountB` reads from its proof for its
contract under that state root, and each of its keys' values what `Spec.Mpt.storageB` reads
from the key's proof under that account's storage root (`Lc.nameHeld`,
`LkdProofs.Lc.SnapshotName.nameHeld_iff`, `snapshot_name_held`): a rule generic in ENS, whose
meaning, the name's resolution or the reverse record's name, is the UI's re-check under the same
root (`ens::forward`, `ens::reverse`, `ens::primary`; [`17-ens.md`](17-ens.md#names-as-snapshot-facts-lc9)).

**The split rule** (`lkd_ui::snapshot::split`): the facts of one block, in order, each name fact
in a record of its own first (LC9, D48), then the account facts then the token facts; a record
takes facts while the next fits within 65,535 bytes, then
the next record starts, each with its own copy of the update and the header; a fact too large for a record of its own (a proof above about
63 KiB with the update and header) is left out. `MakeSnapshot`'s records have one fact each
(`Record` carries at most 65,463 bytes of record, lcproto's body less the identity); the UI merges
those of one block (the same chain, number, time, tag and header, the first record's update kept)
into as few records as fit. On mainnet a finality update is about 2 KB, a header about 600 bytes
and an account proof about 4 KB: some fifteen addresses a record.

The phase (`Wire.phaseOk`, `lc_wire::PHASE_*`; `8` to `255` reserved):

| Phase | Name | When |
|---|---|---|
| 0 | Endpoint | No light client runs (no checkpoint, or a chain `Forks` lacks): accounts are proved at one endpoint's head, on its word (was Quorum until 2026-10-28) |
| 1 | Checking evidence | `Load`'s check of the evidence copies runs |
| 2 | Syncing | No store yet (no copy loaded; the checkpoint's bootstrap is to be fetched, LC6), or nothing anchored |
| 3 | Anchored | An anchor within `MAX_AGE` |
| 4 | Halted | A conflict halted the store |
| 5 | Too old | `effNow − slotTime(finalized slot) > MAX_AGE` |
| 6 | Clock behind | Anchored, the clock's slot before the newest verified attested slot |
| 7 | Unknown fork | Every source that answers, at least two, tags slots with a fork the table lacks (set by LC6's planner) |

They are checked in that order, from halted down: a halted store is said halted whatever its
age. Once a light client runs, every answer's identity names the chain's genesis validators root
and the checkpoint. The codes:

| Code | Name | Meaning |
|---|---|---|
| 1 | `Malformed` | The query frame did not decode |
| 2 | `Unsupported` | A query this `lkd-lc` does not answer yet |
| 3 | `Unreachable` | netd answered `Failed`, whatever its code, or did not answer in time |
| 4 | Retired | Was `NoQuorum` (fewer than k of the n endpoints reported one block hash), retired with the quorum on 2026-10-28: never answered, never reused; a frame carrying it still decodes |
| 5 | `Refused` | The bytes netd forwarded failed a check: the header does not verify against its own hash, or the proof does not prove the account under its state root |
| 6 | `Busy` | Too many queries wait; ask again |
| 7 | `NotAnchored` | The light client runs and cannot anchor: no store yet, syncing, checking evidence, halted, too old, clock behind or unknown fork, exactly when `Status`'s phase is not `3` Anchored (LC6). The client falls back to one endpoint's path, yellow |
| 8 | `NotPinned` | `Token`, `Pin` or `Pool` names an index the chain's table lacks (LC7, D28) |
| 9 | `NodeWindow` | Your own node refused a proof the read needed: its state pruned, or the block outside its proof window (the channel's `Window`, D42). The read ends at once; the UI names the refused read's block ([the node's proof window](#the-nodes-proof-window)) |

`0` and `10` to `255` are reserved. Without a light client (no checkpoint, or a chain `Forks`
lacks: phase `0`), `Account` is answered as in LC1, never `NotAnchored`. `Error(NotAnchored)` on
Sepolia with no store yet, gvr `d8ea…8078` and checkpoint `R`, is `00 00 00 4a 84 00 00 00 00 00
aa 36 a7`, the gvr's 32 bytes, `R`'s 32, `07`.
`Status` is `00 00 00 01 01`; `Account` of twenty `0x42` bytes is `00 00 00 15 02` and the
address; `Error(Unsupported)` on Sepolia with no light client is `00 00 00 4a 84 00 00 00 00 00
aa 36 a7`, 64 zero bytes, `02`; `CheckSnapshot` of the record `ab cd` is `00 00 00 03 08 ab cd`.
`CacheRead` of cache `01 02` (tree leaves, pool 2) from item 7 is `00 00 00 07 0a 01 02 00 00 00
07`; `MakeTokenSnapshot` of twenty `0x42` bytes is `00 00 00 15 0d` and the owner. With Sepolia's
identity, a genesis validators root of 32 `d8` bytes and a checkpoint of 32 `cc` bytes, and the
anchor of block 7 (hash 32 `77` bytes, 400 of 512 signers, slot 9, beacon root 32 `bb` bytes,
finalized 5, 1,500 ms old, neither final nor parent): `Token` of token 0 for an owner of twenty
`42` bytes, its contract twenty `1c` bytes, matched, under the header `f9` and the account proof
`aa`, one slot of value 32 `05` bytes and proof `cc`, is `00 00 01 0c 85`, the identity, the
anchor, `00 00`, the owner, the contract, `00 00 00 00 00 01 f9 00 00 00 01 aa 01`, the value,
`00 00 00 01 cc` (268 bytes of body); `CacheStored` of cache `01 02`, 5 staged and 3 committed at
block 100, is `00 00 00 5b 8c`, the identity, `01 02 00 00 00 05 00 00 00 03 00 00 00 00 00 00
00 64`. Every new frame's example is a theorem of `LkdProofs.Lc.Wire` (`layout_cacheRead` to
`layout_tokenRecord`, the identity and anchor `layout_exampleHead`). LC9's: `BlockHash` of block
`01 02 03 04 05 06 07 08`, final, is `00 00 00 0a 0f`, the number, `01`; `Head` of the anchor is
`00 00 00 02 10 00`; with the identity and anchor above, block 7 being P, `BlockHash` of block 6,
proved, its hash 32 `66` bytes, under P's header `f9` and the history proofs `aa` and `ab`, is
`00 00 00 e8 8e`, the identity, the anchor, `00 00 00 00 00 00 00 06 00`, the hash, `00 00 00 01
f9 00 00 00 01 aa 00 00 00 01 ab` (232 bytes of body); block 8, ahead, is `00 00 00 e5 8e`, the
identity, the anchor, `00 00 00 00 00 00 00 08 01` and 44 zero bytes (229); `Head` of P with its
header `f9` is `00 00 00 b5 8f`, the identity, the anchor, `00 00 00 01 f9` (181);
`Error(NodeWindow)` is `00 00 00 4a 84`, the identity, `09` (`layout_blockHashQuery` to
`layout_nodeWindow`).

**The channel.** Datagrams of at most `MAX_DATAGRAM` = 61440 bytes (60 KiB) each way, with no
length prefix: a datagram arrives whole. Every datagram starts with the generation (8) and the
tag (4), then a kind byte. The generation is `lkd-lc`'s (from its argument vector); the tag is
`lkd-lc`'s name for one request, which every reply and every `FetchPage` for it repeats.

| Kind | Request | Fields after the kind | Datagram |
|---|---|---|---|
| `0x01` | `FetchPage(k)` | page (4) | 17 |
| `0x10` | `ProvedAccount(a)` | address (20) | 33 |
| `0x11` | `ElProof(attempt, h, a)` | attempt (1), block hash (32), address (20), keys (1: `0`, none) | 67 |
| `0x12` | `ElHeader(attempt, h)` | attempt (1), block hash (32) | 46 |
| `0x13` | `ElBlock(attempt, tx, h)` | attempt (1), tx hash (32), block hash (32) | 78 |
| `0x14` | `ElReceipts(attempt, tx, h)` | attempt (1), tx hash (32), block hash (32) | 78 |
| `0x15` | `ElStorage(attempt, h, keys)` | attempt (1), block hash (32), key set (1, then its arguments) | 49 to 87 |
| `0x20` | `Bootstrap(source, root)` | source (1), block root (32) | 46 |
| `0x21` | `Updates(source, p, c)` | source (1), start period (8), count (1: 1 to 14) | 23 |
| `0x22` | `FinalityUpdate(source)` | source (1) | 14 |
| `0x23` | `OptimisticUpdate(source)` | source (1) | 14 |
| `0x24` | `BlockRoot(source, slot)` | source (1), slot (8) | 22 |

The EL requests (10i), by block hash (EIP-1898): `ElProof` is `eth_getProof(a, [], {"blockHash":
h})` on `Account(a)`, `ElHeader` is `eth_getBlockByHash(h, false)` on `Head`. `attempt` is `0` the
first time `lkd-lc` asks, and one more each time it asks again after a refusal or a timeout; netd
picks the endpoint from it (open decision 11: for a proof, the endpoint kept for the address,
then the next ones in turn). `ElProof`'s `keys` stays `0`, none, any other value refused: LC7's
typed key sets travel in a kind of their own, `ElStorage` (D10, below), never a key `lkd-lc` or
netd picks. The beacon requests (10i's `Beacon` class) name the beacon source by
its place in the configuration (`source`); `Updates` asks `updates?start_period=p&count=c`,
`BlockRoot` asks `blocks/{slot}/root` (`--propose`). G12's block by hash, with its
transactions, and its receipts (LC8) are `ElBlock`, `eth_getBlockByHash(h, true)`, and
`ElReceipts`, `eth_getBlockReceipts(h)`: by hash only, on the transaction's `Broadcast(n)` (D4),
`tx` naming the transaction for netd's group and never sent. `ElStorage` is `eth_getProof` of its
key set's contract and keys at `h` (EIP-1898), on the key set's group: `LkdLc.Pins` derives both
(`lkd_verified::pins::keys_of` in netd). The head cross-check's `eth_getBlockByNumber` is the
UI's, on netproto (D35), and has no kind here. Any other kind is reserved too. netd answers a
request it does not decode, a reserved kind or value included, with `Failed(Malformed)`, and
sends nothing for it.

An `ElStorage` key set is its tag, then its arguments (`Channel.KeySet`, `keySetBytes`):

| Key set | Lean `Channel.KeySet` / Rust `KeySet`, const | Arguments | Request | Keys (`LkdLc.Pins`) | Contract | Group |
|---|---|---|---|---|---|---|
| 1 | `.pin i` / `Pin`, `KEYS_PIN` | index (2) | 37 | `pinSlots` | the pin's | `Shared` |
| 2 | `.pinImpl i` / `PinImpl`, `KEYS_PIN_IMPL` | index (2) | 37 | none | the pinned implementation | `Shared` |
| 3 | `.token i owner` / `Token`, `KEYS_TOKEN` | index (2), owner (20) | 57 | `tokenSlots` | the token's pin's | `Account(owner)` |
| 4 | `.poolHead i` / `PoolHead`, `KEYS_POOL_HEAD` | index (2) | 37 | `headSlots` | the pool's pin's | `Shared` |
| 5 | `.poolRoot i x` / `PoolRoot`, `KEYS_POOL_ROOT` | index (2), x (8) | 45 | `rootSlot x` | the pool's pin's | `Shared` |
| 6 | `.history n` / `History`, `KEYS_HISTORY` | n (8) | 43 | `historySlot n` | EIP-2935's | `Shared` (LC9, D38: issued by `lkd-lc` for `BlockHash` at the proving header's EL hash, which picks its endpoint; allocated on `Head` for D25, never issued there) |
| 7 | `.historyFor n tx` / `HistoryFor`, `KEYS_HISTORY_FOR` | n (8), tx hash (32) | 75 | `historySlot n` | EIP-2935's | `Broadcast(n_tx)` |

The request column counts the kind, the attempt and the block hash (34 bytes) with the key set.
Key-set tags `0` and `8` to `255` are refused (`8` and `9` reserved for D32's follow-up).
`lkd-lc-core`'s `request_len` reads the kind and, for `0x15`, the key-set tag at offset 34.
`TooLarge` (7) also answers `ElReceipts` over `MAX_BLOCK_BODY` and an `ElStorage` proof over a
page.

| Kind | Reply | Fields after the kind | Datagram |
|---|---|---|---|
| `0x81` | `Page` | source (1), page (4), last (1: `0` more pages follow, `1` the last), payload (the rest, at most `MAX_PAGE` = 61421 bytes) | 19 + p |
| `0x82` | `Failed(code)` | code (1) | 14 |
| `0x83` | `Started` | none | 13 |

| Code | Name | Meaning |
|---|---|---|
| 1 | `Malformed` | The request did not decode; netd sent nothing for it |
| 2 | `Denied` | The egress policy refused it |
| 3 | `Unreachable` | No source could be reached within the deadline |
| 4 | `Node` | A source answered with an error, or with something not of the shape asked |
| 5 | Retired | Was `NoQuorum` (fewer than k of the n sources reported one block hash), retired with the quorum on 2026-10-28: never sent, never reused; `lkd-lc` reads it as any other failure, `Unreachable` |
| 6 | `NoPage` | A `FetchPage` for a tag or page netd does not hold |
| 7 | `TooLarge` | The response exceeds `MAX_RESPONSE`, the 8 MiB netd holds of one |
| 8 | `TimedOut` | Written by `lkd-lc`'s shell, never by netd: no reply within the deadline |
| 9 | `NotSent` | Written by `lkd-lc`'s shell: sending the request would have blocked |
| 10 | `NotFound` | The source has no such object (HTTP 404): an empty slot for `BlockRoot`, a bootstrap or a period it does not serve; for `ElHeader`, a block the endpoint does not have (`eth_getBlockByHash` answered `null`) |
| 11 | `NotSsz` | The source answered JSON netd could not re-encode as SSZ: a version it has no SSZ type for |
| 12 | `Window` | Your own node refused the proof: its state pruned, or the block outside its proof window (D42). Written only for a request your own node served (source `255`); a public endpoint's refusal is `Node` (4), and the next endpoint is asked |

netd sends `Started` as it begins serving a decoded `Fetch` (never a `FetchPage`, never a
datagram it does not decode), dropped if it would block; `lkd-lc`'s shell takes it, and the core
never sees it (D43). Every other reply kind, and the codes `0` and `13` to `255`, are reserved.

A response is the payloads of its pages, page 0 first, up to the one marked last; `lkd-lc`
pulls page `k + 1` with `FetchPage(k + 1)` under the same tag. A response is at most
`MAX_RESPONSE` = 8 MiB, the most netd holds of one response (D12: only responses longer than one
page are held, at most 4 and 24 MiB together, each until its last page is pulled, the least
recently paged evicted first). `source` names the source the
response came from by its place in the configuration; `ProvedAccount` names the
endpoint whose proof it carries, by its place among the public endpoints, `255` for your own
node (in hybrid mode); an EL request's names the endpoint that answered, `255` for
your own node; a beacon request's is the source it named.

| Request | Response | At most |
|---|---|---|
| `ElProof` | the account as the endpoint's JSON gives it: nonce (8), balance (16), storage root (32), code hash (32); then the account proof's nodes, one after the other (the rest) | one page |
| `ElHeader` | the header's RLP, netd's re-encoding of the JSON (untrusted): the whole response | 2,048 bytes |
| `ElBlock` | `BlockBody`: N's header length (4: 1 to 2,048) and RLP, netd's re-encoding (untrusted); a flag (1): `0` the transactions list's RLP follows (the rest), `1` too large (`MAX_BLOCK_BODY`, D11), nothing follows | `MAX_RESPONSE` |
| `ElReceipts` | the receipts list's RLP, netd's re-encoding (untrusted): the whole response | `MAX_RESPONSE` |
| `ElStorage` | `StorageProof`: the account as the endpoint's JSON gives it, nonce (8), balance (16), storage root (32), code hash (32); the account proof's length (4) and nodes; the key count (1: 0 to 8); per key, in the key set's order, the value (32), the slot proof's length (4) and nodes | one page |
| `Bootstrap`, `FinalityUpdate`, `OptimisticUpdate` | name length (1: 1 to 16), the fork's name (the `Eth-Consensus-Version` value as received, or the JSON's `version`), the SSZ (the rest: as received, or netd's re-encoding of the JSON's `data`) | `MAX_RESPONSE` |
| `Updates` | form (1), the chunks (the rest). Form `0`: the SSZ answer as received, chunks `u64le(4 + s)`, digest (4), SSZ (s) (`LkdLc.Ssz.parseUpdates`, 25a). Form `1`: netd's re-encoding of a JSON answer, one chunk per item, `u64le(1 + s)`, fork (1: `0` Electra, `1` Fulu, `2` Gloas, as the evidence numbers them; the others refused), SSZ (s) (`LkdLc.Ssz.parseForkUpdates`) | `MAX_RESPONSE` |
| `BlockRoot` | the root (32), the JSON's `data.root` | 32 bytes |

After the generation and the tag, `Updates` from source 0 for 14 periods from 1366 is `21 00`,
`00 00 00 00 00 00 05 56`, `0e`, and `FinalityUpdate` from source 3 is `22 03`; a re-encoded
chunk of fork 2 and SSZ `aa bb` is `03 00 00 00 00 00 00 00 02 aa bb`. `ElBlock` at attempt 0
for the transaction of 32 `7a` bytes in the block of 32 `66` bytes is `13 00`, the transaction's
hash, the block's; `ElStorage` at attempt 0 at the block of 32 `77` bytes, of token 1's key set
for an owner of twenty `42` bytes, is `15 00`, the block's hash, `03 00 01`, the owner. A
`BlockBody` of the header `f9` and the transactions list `c0` is `00 00 00 01 f9 00 c0`, and too
large `00 00 00 01 f9 01`.

The account fields an `ElProof` response carries are the endpoint's word, which `lkd-lc` never
answers with: it reads the account from the proof (`El.Mpt.accountB`), and a difference marks
the endpoint faulty. netd keeps no fork table: it forwards the name a source gave, and re-encodes
only the versions whose SSZ types it has (`NotSsz` otherwise); `lkd-lc` checks the name, the
digest or the fork byte against `Forks` at the attested slot (25a), so an unknown name reaches it
and counts toward "unknown fork".

`ProvedAccount`'s response is what `proved_account` gathers
(`crates/netd/src/upstream.rs`), in this layout rather than netproto's: the header's length (4)
and RLP, the head one endpoint gave (the first that answers, the next one's when it fails) or
your node's, then the proof's length (4) and nodes one after the other. It carries no reports
and no threshold since 2026-10-28 (no quorum): `lkd-lc` checks the header against its own
Keccak-256. It is at most one page, 8 + H + P ≤ 61421, so the `Account` answer built from it
always fits lcproto's body (234 + H + P ≤ 65536).

**`lkd_lc_step`'s inputs** are one per call, a tag then its fields, with no length prefix: the
call gives the whole input. `now` is milliseconds since the Unix epoch.

| Tag | Input | Fields after the tag | Bytes |
|---|---|---|---|
| `0x01` | `Load(copyA, copyB, conflict, now)` | now (8), copy A's length (4) and bytes, copy B's length (4) and bytes, the conflict block's length (4) and bytes | 21 + a + b + c |
| `0x02` | `Tick(now)` | now (8) | 9 |
| `0x03` | `Fetched(tag, source, page, last, bytes)` | tag (4), source (1), page (4), last (1), the page's payload (the rest, at most 61421) | 11 + p |
| `0x04` | `Failed(tag, code)` | tag (4), code (1): the channel's codes | 6 |
| `0x05` | `Query(conn, frame)` | connection (4), the lcproto frame as read, its length included (the rest, at most 65540) | 5 + f |
| `0x06` | `Closed(conn)` | connection (4) | 5 |

`0x07` and above are reserved. Each evidence copy is at most `MAX_COPY` = 16 MiB, which the
shell checks before reading the file. A `Query` carries the frame undecoded: the core decodes
it and answers `Error(Malformed)` to a frame that does not decode, so the shell never needs to.

**Effects** come back from each call in order, each a tag then its fields, with nothing between
them and nothing after the last:

| Tag | Effect | Fields after the tag | Bytes |
|---|---|---|---|
| `0x01` | `Fetch(tag, request)` | tag (4), the request's length (2), the request: a channel request after its tag, kind first, never `FetchPage` | 7 + r |
| `0x02` | `FetchPage(tag, k)` | tag (4), page (4) | 9 |
| `0x03` | `Answer(conn, answer)` | connection (4), the lcproto answer frame, its 4-byte length included | 9 + L |
| `0x04` | `Persist(copy, payload)` | copy (1: `0` A, `1` B), payload length (4), payload (at most 16 MiB) | 6 + p |
| `0x05` | `PersistConflict(payload)` | payload length (4), payload (at most 16 MiB; the shell refuses one past the 64 KiB region) | 5 + p |
| `0x06` | `ClearConflict` | none | 1 |
| `0x07` | `Status(phase)` | phase (1: `0` to `7`, lcproto's), told when it changes | 2 |

`0x08` and above are reserved. LC6 changes neither table: a `Fetch` carries LC6's request
kinds as it carries `ProvedAccount`'s, and `Fetched` the source a page came from; nor do LC7 and
LC8, whose kinds a `Fetch` carries too, at most 75 bytes of request (an `ElStorage` of a
`HistoryFor` key set, `Channel.fetchBytes_length_le`). The shell writes a `Fetch` as the datagram
generation ‖ tag ‖ request, and a `FetchPage` as generation ‖ tag ‖ `01` ‖ page; it writes
`Persist`'s payload at the start of its copy's region, `PersistConflict`'s at the start of the
conflict block's, zeroes the conflict block on `ClearConflict`, and says the phase `Status` names
on standard error. Every effect's length follows from its tag and the lengths it carries, so one
byte string names at most one list of effects. LC5's three, in the layout's example
(`Lkd.Lc.layout_evidence`, `lkd_lc_core`'s `documented_evidence`): `PersistConflict` of `01 02`,
`ClearConflict`, `Status` of phase 3 is `05 00 00 00 02 01 02 06 07 03`.

**`lkd_lc_init`'s configuration** is 57 bytes, every 57-byte string one
(`LkdLc.Ffi.decodeConfig`, `lkd_lc_core::Config`):

| Offset | Width | Field |
|---|---|---|
| 0 | 8 | chain id |
| 8 | 32 | checkpoint root, zero when none is set |
| 40 | 1 | beacon sources configured |
| 41 | 8 | generation, which the shell writes in every datagram |
| 49 | 8 | the sequence of the conflict block to clear (`lc_clear_conflict`, `--clear-conflict`), zero for none (LC5) |

A light client runs when the chain is one `LkdLc.Forks` knows and the checkpoint is not zero; the
sources and the generation are LC6's. A `dev-insecure` `lkd-lc` may start with
`lkd_lc_init_dev` instead (`LkdLcDev.Ffi`): the same 57 bytes, then 48 bytes naming the fake
beacon's chain, the genesis time (8), the genesis validators root (32) and the Gloas fork's epoch
(8, `FAR_FUTURE_EPOCH` for none); with a checkpoint, the light client then runs on the development
table, whatever the chain id. Sepolia with no checkpoint, two sources, generation 1 and
no conflict to clear is `00 00 00 00 00 aa 36 a7`, 32 zero bytes, `02`,
`00 00 00 00 00 00 00 01`, 8 zero bytes.

**What 25o and 25q prove**: for each codec, decoding an encoding gives the value back,
decoding is canonical (what decodes is the encoding of what it decodes to), encoding is
injective, and every encoding fits its cap; the effects' encoding is injective over lists;
`lc_wire` and `lc_channel` compute the `LkdLc.Wire` definitions on every input; the runtime's
`ByteArray` decoders and encoders are the list ones. LC6's frames (the queries and answers
`CheckSnapshot`, `Account` of kind 2 and `Snapshot`; the requests `ElProof` to `BlockRoot`;
the codes `NotFound` and `NotSsz`; the responses of `ElProof`, `Bootstrap` and the other two
objects, and `Updates`, and the re-encoded chunks of form `1`) are proved the same way; the
`ElHeader` and `BlockRoot` responses are bytes with a cap, which `lkd-lc` reads as they are.
LC7's and LC8's frames (the queries `CacheRead` to `MakeTokenSnapshot`; the answers `Token` to
`Included` and `CacheChunk` to `TokenRecord`, with their values; the code `NotPinned`; the
requests `ElBlock`, `ElReceipts` and `ElStorage` with its seven key sets; the responses of
`ElStorage` and `ElBlock`) are proved the same way, each with its example and the answers with
their bodies' formulas (`body_token` to `body_tokenRecord`); and what decodes is a value the
layout carries (`decodeQuery_wf`, `decodeAnswer_wf`, `decodeFetch_wf`, `decodeRequest_wf`,
`decodeStorageProof_wf`, `decodeBlockBody_wf`). The `ElReceipts` response is bytes with a cap.
LC9's frames (the queries `BlockHash` and `Head`; the answers `BlockHash` and `Head`, with their
values and an absent part empty; the code `NodeWindow`; the reply `Started` and the code
`Window`) are proved the same way, by the same statements restated for them, each with its
example (`layout_blockHashQuery` to `layout_nodeWindow`, `Channel.layout_started`,
`Channel.layout_window`), the answers with their bodies' formulas (`body_blockHash`,
`body_head`) and `Started` with its 13 bytes (`Channel.replyBytes_started`); what decodes is a
value the layout carries (`parseBlockHash_wf`, `parseHead_wf`), and an answer a handler checks
before it answers is one the frame carries (`Lc.fitsBlockHash_wf`, `Lc.fitsHead_wf`). Kani
checks both queries' round trip, `BlockHash`'s and `Head`'s parsers on frames of their fixed
part and up to 4 more bytes, and every reply's round trip, `Started` included; a longer
certificate's totality is the refinement's.

### Sandboxes

**`lkd-lc` (26a) follows `keyd`'s order exactly** (`crates/keyd/src/sandbox/linux.rs:1-30`,
`:148-173`, `:197-198`), with **no mount view**: the view has no `/proc`
(`crates/sandbox/src/lib.rs:9`), and with it `settle_threads` would return without waiting.

1. Single-threaded still: open, lock and read the evidence; when serving, open, lock and load
   the public caches' file (G19; none in the one-shots); bind `lkd-lc.sock`; take the
   channel's descriptor; set `RLIMIT_FSIZE` (320 MiB since LC7: above the largest chain's
   caches file, mainnet's 300 MiB, sparse); deny `io_uring_setup`, `io_uring_enter` and
   `io_uring_register` with `ENOSYS` on every thread and refuse a ring already open
   (`sandbox::disable_io_uring`, as master's `keyd` does since 9b141045: libuv's SQPOLL ring
   would otherwise submit file operations from a kernel thread no later filter reaches; libuv
   falls back to epoll); enter a network namespace only (`lkd_sandbox::namespaces(true,
   false)`).
2. Start Lean's runtime.
3. Deny `io_uring` again and refuse an open ring (a caller that missed step 1), then wait
   until every other thread sits in its event loop, reading `/proc`, through
   `settle_threads`, `in_loop_wait` and `LOOP_WAITS`, moved from `keyd`'s sandbox into
   `lkd_sandbox::settle` (safe code) rather than copied; `keyd` calls it from there too (done in
   LC1, the move alone).
4. Not dumpable, `RLIMIT_CORE = 0`, `no_new_privs`; the parent-death signal is asked first
   thing at start, before any thread, as `keyd` asks it.
5. Landlock: no file access, no TCP, and (ABI 9's `ResolveUnix`, with abstract Unix sockets
   scoped out, as netd's; after the second review, 2026-10-28, which found `ABI::V7` handled no
   pathname socket) no pathname socket's `connect` or `sendto`. It binds the calling thread
   only, so the runtime's thread is held by step 6 alone, as in `keyd`.
6. Seccomp on every thread (`TSYNC`), killing on anything but `keyd`'s `ALLOWED` and
   `ALLOWED_ARCH` (`linux.rs:57-95`) less `accept`, `mlock`, `getpid` and `fsync` (LC1 left
   out `pread64` too; LC7 allows it for the public caches' reads in place):
   so `accept4`, `brk`, `clock_gettime`, `close`, `epoll_pwait`, `exit`, `exit_group`,
   `fdatasync`, `futex`, `getrandom`, `getsockopt` (`SO_PEERCRED`, the peer-uid check),
   `madvise`, `mmap`, `mprotect`, `mremap`, `munmap`, `ppoll`, `pread64`, `pwrite64`, `read`, `recvfrom`,
   `rt_sigprocmask`, `rt_sigreturn`, `sched_yield`, `sendto`, `shutdown`, `sigaltstack`, `write`,
   `writev`, and `epoll_wait` and `poll` on x86-64 (`crates/lc/src/sandbox.rs`, `ALLOWED`), with
   `fcntl` only as `F_GETFD`: std's `OwnedFd` calls it before closing a descriptor in a debug
   build (`debug_assert_fd_is_open`), as the session test found; `epoll_pwait2` was not needed;
   and `sendto` only with no address (`dest_addr` null: std's `send`, the channel's datagrams to
   its peer). Without that condition a `sendto` with an address on the channel, a connected
   datagram socket, reached any pathname datagram socket the user may write to (journald's,
   `/dev/log`), and abstract ones where there is no network namespace: the second review's
   finding, tested since (`sendto-path`). No call that takes a path or a socket address, and no
   `socket`, `connect`, `bind`, `ioctl` or `execve`, so `lkd-lc` reaches no file but its evidence
   and its caches file, through the descriptors it holds, no socket but its listener, the
   connections it accepts and the channel, and not `keyd`'s. The uid the peer check
   compares with is read before the filter, which kills `getuid`.

The one-shots run in the same sandbox, `--check` with the evidence opened `O_RDONLY`,
`--propose` with it read-write under the same `flock` (it persists the bootstrap it verified).
A ten-minute soak of the Lean runtime under this filter fixes the list (`just e2e-lc-soak`; `just
e2e` soaks 30 s). The calls std does not wrap, the sandbox's and the shell's (`peer_uid`,
`socket_type`, `accept_nonblocking`, `poll`, `umask`, `set_non_dumpable`, `limit_file_size`:
`RLIMIT_FSIZE` with `SIGXFSZ` ignored), are additions to `crates/sandbox/src/sys.rs`, so
`crates/lc` has no `unsafe` code (open decision 14, as adopted), with a second reviewer; the
channel is taken from standard input with std alone, as netd takes it. Tested in child processes
(`crates/lc/tests/sandbox.rs`): under Landlock no path opens, the evidence file's included, while
the evidence is written through its descriptor; under the filter a file made beside the evidence
kills, and in the full sandbox a socket of any family does; the runtime's thread, not yet run,
settles; `RLIMIT_FSIZE` answers `EFBIG` without killing, and a byte just below it is written;
the public caches' file, opened before the full sandbox, is appended to, committed and read
back through its descriptor, while opening it by its path kills; and a whole `Status` and
`Account` session, a fetch over the channel and a stale generation's reply dropped, runs in the
sandbox. Since LC7's `RLIMIT_FSIZE` covers the caches, the evidence's writer is tested to keep
to its own layout (`evidence::tests::writes_stay_in_the_layout`).

**`lkd-beacon` (26c, decision 28)**, netd's helper on the direct route, in this order, each step
before it reads a request (`lkd_netd::direct::sandbox`, safe code over `landlock`, `seccompiler`,
`lkd_sandbox::mount_view` and netd's `sys`, so no new `unsafe` module):

1. First thing, the parent-death signal (it dies with netd), then, while single-threaded, its
   channel taken from standard input, `/etc/resolv.conf` read, the sources parsed and checked by
   the egress policy (and, in a `dev-insecure` build only, `--test-root` and `--dev-direct`).
2. A mount view with nothing in it (`mount_view(&[], false)`): a user namespace mapping only its
   uid and gid, a mount namespace whose root is an empty read-only tmpfs, the host's network
   namespace kept, since it needs it. Where user namespaces are refused it says so and goes on.
3. Not dumpable, `RLIMIT_CORE = 0`, `no_new_privs`.
4. Landlock: every file access handled and none allowed; TCP bind none; TCP connect to 443 and 80
   only (ABI 4, Linux 6.7), and the `dev-insecure` test ports; abstract Unix sockets and signals
   scoped (ABI 6). Best effort: an older kernel enforces what it has, and the report says what it
   could not (the ports, on a kernel before 6.7).
5. Seccomp, killing the process on any call off its allowlist: `socket` for `AF_INET` and
   `AF_INET6` only, `connect`, `bind` (the resolver's UDP socket, which std binds before it
   connects; Landlock refuses every TCP bind), `read`, `write`, `writev`, `recvfrom`, `sendto`,
   `ppoll` (and `poll` on x86-64), `getsockopt`, `setsockopt`, `ioctl` as `FIONBIO`, `fcntl` as
   `F_GETFD`, `close`, `shutdown`, the allocator's (`brk`, `mmap`, `mremap`, `munmap`,
   `mprotect`, `madvise`), `futex`, `clock_gettime`, `getrandom`, `rt_sigreturn`,
   `rt_sigprocmask`, `sigaltstack`, `sched_yield`, `exit`, `exit_group`. No call that takes a
   path, no `listen`, `accept`, `execve`, `clone` or `ptrace`: no `AF_UNIX` socket, so not tor's
   SOCKS socket, netd's, `keyd`'s or `lkd-lc`'s. The Landlock ABI is read before the filter.

Then it sends its ready frame, with the report, and serves netd until its channel closes. Tested
in child processes (`crates/netd/tests/direct.rs`): in the full sandbox, with one port added as
`--dev-direct` adds the fake beacon's, a TCP connect to that port succeeds and one to another port
is refused (`EACCES`, where the kernel has Landlock's network rules); the resolver gets a fake DNS
server's public answer over UDP and refuses its loopback one; an `AF_UNIX` socket kills, opening
`/etc/hostname` kills; and `lkd-beacon` itself, started as netd starts it, is ready with its
report, runs with `Seccomp: 2` and `NoNewPrivs: 1`, fails a request it cannot fulfil within the
deadline, and exits when netd's end closes. Its forwarding and frames are unit-tested
(`direct::helper`, `beacon`'s `direct_sources_are_forwarded_typed`), and its fetching against a
plain fake beacon through the local map, with a name resolving to loopback refused
(`direct::fetch`); TLS through the map is `lc-direct`'s.

**netd** keeps its filter and its single thread; its loop and `sys.rs` change. 19a is restated
for the inherited channel, for tor's SOCKS directory in its view when a beacon source needs tor
(over IPC, as hybrid mode's view holds it), and, on the TCP route, for a second Landlock port, a
beacon node's on loopback. **The UI and the window**: 19b is restated, with a second reviewer,
since `connect` now also reaches `lkd-lc.sock`, in the runtime directory their view holds.

**The launcher.** Start order: tor, netd; then, before `keyd` asks (so 17c holds), either
`lkd-lc --propose` (no checkpoint, or a store past `MAX_AGE` or halted; after up to 60 s of
tor's bootstrap; the user may skip) or `lkd-lc --check`, in the background while `keyd` asks
(open decision 7); then the configuration is written, and `lkd-lc`, `keyd` and the UI start. A
one-shot never runs beside the daemon, whose channel end it would share. It writes its root as
one fixed-format line on a pipe, never on the terminal; the launcher parses it with
`lkd_verified::config`'s root parser and itself prints the root it will write, in groups of
four: that text is what the user compares. The launcher creates `<home>/lc` with mode `0700`;
`paths::BINARIES` (`crates/launch/src/paths.rs:13`) gains `lkd-lc`. `lkd-lc` prints `ready`
after binding and entering its sandbox, then checks the evidence behind "checking evidence". It
is restarted as netd is, each start with the next generation (1, 2, …), so that it drops what
netd answers its predecessor; after a pause of 1 s doubled while it keeps stopping within a
minute of its start, up to 60 s, said once a stop ("lkd: lkd-lc stopped (…); starting it
again", "keeps stopping" after three in a minute); `Relay` holds a set of quiet daemons instead
of one, since netd and `lkd-lc` restart on threads of their own. In LC1, which has no checkpoint
and no one-shot, `lkd-lc` starts after netd and before `keyd`, and the wallet goes on without it
when it does not start. It exits with its parent and is stopped with netd and tor; a restart of
netd costs it nothing, the one a settings change from the window asks on `lkd`'s control socket
included ([`03-wallet-ui.md`](03-wallet-ui.md)). A new chain there, which ends the UI with status
11, starts `lkd-lc` again at once on that chain, with its next generation and no pause, and `lkd`
waits for its `ready` (up to 10 s) before it starts keyd. `ui_command` needs no new environment. A `dev-insecure` `lkd start
--tamper-lc` passes `--tamper-certificates` on.

**The command line** never waits for `lkd-lc`: while it checks evidence, syncs or is down,
`balance`, `send`, the token send, `discover`, `resume`, `speed-up` and `cancel` use today's
reads and print the label on standard error ("on rpc1.test's word, not anchored: light client
checking evidence"); `--wait` waits up to 60 s for an anchor; `lkd balance` prints the label
after the amount. `lkd status <hash>` asks netd for the receipt, then `lkd-lc` for `Included`:
"mined (proved)" or "mined (the node's word)" exits 0, or 5 when the transaction failed; "seen,
not yet proved" exits 3; "not provable" and "settled by nonce, inclusion unproved" print their
own lines, with exit codes named in [`03-wallet-ui.md`](03-wallet-ui.md). The light client's own
state is in Settings and on the overview; `lkd status` without a hash (LC1) says whether
`lkd-lc` answers and its phase ("lkd-lc running, phase endpoint: …"), or exits 1 saying it is not
running, or answers for another chain.

## The protocol

> **leanLight, 2026-11-09.** leanLight's store now keeps the specification's whole
> `LightClientStore` (the optimistic header and both participation counters included), checks
> `current_slot >= signature_slot` and `update.next_sync_committee == store.next_sync_committee`
> as `validate_light_client_update` does, and has the specification's forced update
> (`Store.forceUpdate`, never called by the client). The sync protocol is transcribed from
> consensus-specs v1.7.0-beta.5 in `proofs/LeanLightProofs/Spec/SyncProtocol.lean`, and the store
> is proved to refine it (`proofs/LeanLightProofs/SyncProtocol.lean`, `reaches_spec`). Where this
> section and that file disagree, the file and its theorems are leanLight's; the departures that
> remain are listed in `LeanLight/Store.lean`. The rest of this section is the design record as
> copied.

Altair's light client sync protocol (`specs/altair/light-client/sync-protocol.md`), as Capella,
Deneb, Electra and Gloas amend it. `lkd` starts from an Electra or later checkpoint and refuses
earlier headers, so only Electra-era and Gloas types run; earlier forks matter only for test
vectors. Fulu has no light-client directory and uses `electra.LightClient*` ("ELECTRA through
FULU").

### Objects

| Object | Electra and Fulu | Gloas |
|---|---|---|
| `LightClientHeader` | `beacon: BeaconBlockHeader` (slot, proposer index, parent root, state root, body root), `execution: ExecutionPayloadHeader` (17 fields, Deneb's), `execution_branch` (4 roots) | `beacon`, `execution_block_hash: Hash32`, `execution_branch` (11 roots); no `execution` |
| `LightClientBootstrap` | `header`, `current_sync_committee`, `current_sync_committee_branch` (6 roots) | the same, branch of 11 roots |
| `LightClientUpdate` | `attested_header`, `next_sync_committee`, `next_sync_committee_branch` (6), `finalized_header`, `finality_branch` (7), `sync_aggregate`, `signature_slot` | branches of 11 and 9; exactly 26,424 bytes |
| `LightClientFinalityUpdate` | an update without the next committee and its branch | the same |
| `LightClientOptimisticUpdate` | `attested_header`, `sync_aggregate`, `signature_slot` | the same |
| `SyncCommittee` | `pubkeys` (512 compressed G1 points, 48 bytes each), `aggregate_pubkey` | the same |
| `SyncAggregate` | `sync_committee_bits` (512), `sync_committee_signature` (a compressed G2 point, 96 bytes) | the same |

Measured sizes: a Fulu bootstrap 25,672 bytes, a finality update 2,090 bytes, an Electra or
Fulu update 26,893 to 26,933 bytes (its `extra_data` varies). Finality and optimistic updates
are processed as full updates with the missing fields empty, as the specification does.

`execution_block_hash` means different things by the header's own slot
(`gloas/light-client/sync-protocol.md:177-244`). From `GLOAS_FORK_EPOCH` on, it is
`body.signed_execution_payload_bid.message.parent_block_hash`, which the specification requires
to equal `state.latest_block_hash`: the **parent** payload's hash, at gindex 2856. A pre-Gloas
header brought into a Gloas container (`upgrade_lc_header_to_gloas`,
`gloas/light-client/fork.md:26-83`) carries the block's **own** payload hash at 812, its branch
normalized to 11 roots, and no payload fields; for the first epochs after the fork, a Gloas
update's finalized header is such a header. So **each header is tagged by its own slot**:
`Parent` when `epoch(header.beacon.slot) ≥ GLOAS_FORK_EPOCH`, else `Own`, for the anchor and
for the finalized header behind `AccountFinal` and "final up to". The store upgrades itself to
the Gloas form when it first accepts Gloas data, as `fork.md` requires of an Electra store, and
keeps headers in that form after; the vectors' `upgrade_store` steps map to that.

### Constants

| Constant | Mainnet preset | Minimal preset (tests) |
|---|---|---|
| `SLOTS_PER_EPOCH` | 32 | 8 |
| `EPOCHS_PER_SYNC_COMMITTEE_PERIOD` | 256 (8192 slots, about 27.3 h at 12 s) | 8 |
| `SYNC_COMMITTEE_SIZE` | 512 | 32 |
| Anchor threshold (`3·bits ≥ 2·size`) | 342 | 22 |
| `MIN_SYNC_COMMITTEE_PARTICIPANTS` | 1 | 1 (`presets/minimal/altair.yaml:22`) |
| `UPDATE_TIMEOUT` | 8192 slots (unused: no forced update) | 64 |
| `DOMAIN_SYNC_COMMITTEE` | `0x07000000` | the same |
| BLS DST | `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_` | the same |
| `MAX_REQUEST_LIGHT_CLIENT_UPDATES` | 128 (lkd asks at most 14) | the same |

Network configuration, not preset: `SLOT_DURATION_MS` is 12,000 on mainnet and on Sepolia
after Gloas (`SECONDS_PER_SLOT` is deprecated and gone from master's `configs/mainnet.yaml`).
EIP-8198 ("Quick Slots", 12 s to 10 s through a `SLOT_DURATION_SCHEDULE`) is considered for
Hegotá and carried in consensus-specs master as a feature, so slot times are a schedule in
`Forks`, not a constant. Sepolia's Gloas sets `SYNC_MESSAGE_DUE_BPS_GLOAS` to 2500, 25% of a
slot, against 3333 before. Servers SHOULD serve bootstraps and best updates for
`compute_min_epochs_for_block_requests()`: 33,024 epochs before Gloas (about 146.8 days, 129
periods), 14,299 under Gloas with mainnet's constants (about 63.6 days, 56 periods).

### Generalized indices

A field's gindex in a bounded container is `next_pow2(n) + i`. Gloas's `BeaconState` and
`BeaconBlockBody` are `ProgressiveContainer`s (EIP-7688, EIP-7495): on their spine, chunk 0
is at 4, chunks 1 to 4 at 40 to 43, chunks 5 to 20 at 352 to 367, chunks 21 to 84 at 2944 to
3007. Recomputed from the field lists, each equal to the specification's constant
(`electra/light-client/sync-protocol.md:86-90`, `gloas/light-client/sync-protocol.md:97-113`):

| Field | Position | Altair to Deneb | Electra, Fulu | Gloas, Heze |
|---|---|---|---|---|
| `finalized_checkpoint.root` | `BeaconState` [20], then `Checkpoint` [1] | 52 → 105 | 84 → 169 | 367 → 735 |
| `current_sync_committee` | `BeaconState` [22] | 54 | 86 | 2945 |
| `next_sync_committee` | `BeaconState` [23] | 55 | 87 | 2946 |
| execution payload (header) | `BeaconBlockBody` [9] | 25 (Capella on) | 25 | none |
| the EL block hash, in the body | Capella, Deneb on: payload [12]; Gloas: `signed_execution_payload_bid` [10] = 357, `.message` 714, `.parent_block_hash` [0] | 412 (Capella), 812 (Deneb) | 812 | 2856 |

`BeaconState` has 24 to 28 fields from Altair to Deneb, 37 in Electra, 38 in Fulu
(`proposer_lookahead` at [37], still depth 6). Branch lengths: Electra and Fulu 6 for each
committee, 7 for finality, 4 for the execution payload; Gloas 11, 9 and 11. Heze keeps
Gloas's positions through `active_fields` gaps (`heze/beacon-chain.md:155,179`), so 735, 2945,
2946 and 2856 hold there; Heze has no light-client directory of its own.
`is_valid_normalized_merkle_branch` requires the leading extra roots of a shorter branch to be
zero (`altair/light-client/sync-protocol.md:334-345`). Finality and committee branches follow
the attested header's fork, being under its state root; an execution branch follows its own
header's slot. The table is pinned once, in `LkdLc.Ssz`, and recomputed from transcribed
`Desc`s with ssz-specs' `getGeneralizedIndex` (25b, `LkdProofs.Lc.SszGindex`): each theorem fixes the
container's transcribed field names, their count and the types on the path, and holds for every
choice of the other fields' types, since a gindex depends on nothing else.

### Forks per chain

Pinned in `LkdLc.Forks` from each network's `config.yaml` (eth-clients at the pinned
commits), with a test that reads those files. `slotTime(slot)` is `compute_time_at_slot_ms`
over the chain's slot schedule and `slotOf` is `compute_slot_at_time_ms` (consensus-specs
master `b834fa8`, `_features/eip8198/beacon-chain.md:81-139`); `MAX_AGE` and `effNow` are in
milliseconds. EL timestamps, in seconds, are compared with `slotTime / 1000`, exact on the
pinned chains: genesis times are whole seconds and slot durations multiples of 1000 ms
(12,000, 10,000, 6,000). For epochs at or after `FULU_FORK_EPOCH`, `compute_fork_digest(gvr,
epoch)` is the first 4 bytes of the fork data root XOR `sha256(u64le(bpo_epoch) ‖
u64le(max_blobs))` (EIP-7892), with `(ELECTRA_FORK_EPOCH, MAX_BLOBS_PER_BLOCK_ELECTRA)` before
the first BPO entry; before Fulu it is the fork data root's first 4 bytes
(`fulu/beacon-chain.md:322-324`). A BPO changes the digest, not the fork version, so the
signing domain does not change. A digest table without the BPO entries refuses valid updates.

**Mainnet (1).** Genesis validators root
`0x4b363db94e286120d76eb905340fdd4e54bfe9f06bf33ff6cf5ad27f511bfe95`, genesis time 1606824023.

| Fork | Epoch | UTC | Version | Digest | Status |
|---|---|---|---|---|---|
| Electra | 364032 | 2025-05-07 10:05:11 | `0x05000000` | `0xad532ceb` | live |
| Fulu | 411392 | 2025-12-03 21:49:11 | `0x06000000` | `0xcc2c5cdb` | live |
| BPO1 (15 blobs) | 412672 | 2025-12-09 14:21:11 | `0x06000000` | `0xcb0d1acc` | live |
| BPO2 (21 blobs) | 419072 | 2026-01-07 01:01:11 | `0x06000000` | `0x8c9f62fe` | live |
| Gloas | not scheduled | | `0x07000000` at `FAR_FUTURE` in consensus-specs; absent from eth-clients/mainnet | | |

Sync domains: Electra `0x07000000ad532ceb9ec5d246daad29da8aa157bfdab35e5f069f9db81f1da754`;
Fulu and its BPOs `0x0700000082fae541f8a3db43adb5e7997ac5f562cf682ce6bc41b8ec28ba1a07`.

**Sepolia (11155111).** Genesis validators root
`0xd8ea171f3c94aea21ebc42a1ed61052acf3f9209c00e4efbaaddac09ed9b8078`, genesis time 1655733600.

| Fork | Epoch | UTC | Version | Digest | Status |
|---|---|---|---|---|---|
| Electra | 222464 | 2025-03-05 07:29:36 | `0x90000074` | `0x14045b5a` | live |
| Fulu | 272640 | 2025-10-14 07:36:00 | `0x90000075` | `0x7e0d3447` | live |
| BPO1 (15 blobs) | 274176 | 2025-10-21 03:26:24 | `0x90000075` | `0xfd32b622` | live |
| BPO2 (21 blobs) | 275712 | 2025-10-27 23:16:48 | `0x90000075` | `0x74d01459` | live |
| Gloas | 353024 (slot 11,296,768; period 1379) | 2026-10-06 13:53:36 | `0x90000076` | `0x669e6c11` | live |

Blob counts from `sepolia/metadata/config.yaml:214-218`. Sync domains: Electra
`0x0700000014045b5a1d8da091c2ee9e635b64eb2f9c81e0683f21dd0491e95aaa`; Fulu
`0x07000000f52c15272cff99835cd05aa522af469210b5b2c8807e372b6b9ca539`; Gloas
`0x07000000e7626d6f8bf835c77cec81870bdf8b4c76c5f6287cec41d72291599d`.

**Hoodi** is a test fixture for the digest code, not a wallet chain (it joins `Spec.Networks`
first if it ever becomes one): chain id 560048, genesis time 1742213400 (1742212800 plus
`GENESIS_DELAY` 600), its genesis validators root and forks from `hoodi/metadata/config.yaml:110`
and `genesis_validators_root.txt`; its Gloas was unscheduled on 2026-10-22 (ACDE #248).

Every digest above was computed from the configurations and reproduces known values (mainnet
phase0 `b5303f2a` and Deneb `6a95a1a9`; Sepolia `a8fee8ee`); mainnet Fulu and BPO2 match
beaconcha.in's table, and each was seen live.

### Bootstrap

`isValidHeader(h)` follows `h`'s own slot: an `electra` header proves `hash_tree_root(execution)`
at gindex 25 (4 roots) under `body_root`; a Gloas header from `GLOAS_FORK_EPOCH` on proves
`execution_block_hash` at 2856 (11 roots); an upgraded pre-Gloas header proves it at 812, its
branch normalized to 11 roots with zero leading roots. `Store.bootstrap(cfg, bootstrap)`
accepts when `isValidHeader(header)`, `hash_tree_root(header.beacon)` is the configured
checkpoint, the current committee is proved by its branch at the fork's gindex under
`header.beacon.state_root`, and all 512 keys pass KeyValidate. The store starts with that
header finalized, that committee current, no next committee, and nothing anchored.

### Validating an update

`Store.validate(store, update)`, the specification's `validate_light_client_update` with the
departures below, every check before BLS:

1. **Form.** The size is within its kind's cap; the bytes decode as the type of the fork
   `Forks` gives for the attested slot, and the source's tag (`Eth-Consensus-Version`, or the
   chunk's digest) names that fork. A tag the table lacks marks the source faulty.
2. **Participation.** `3·popcount(bits) ≥ 2·SYNC_COMMITTEE_SIZE` (342 of 512).
3. `signature_slot > attested slot ≥ finalized slot`.
4. **No skipped period.** The signature's period is the store's, or the next when the next
   committee is known.
5. **Relevance.** The attested slot is past the store's finalized slot, or the update brings
   the next committee the store lacks, for the store's period. Conflicts are compared before
   this filter ([Conflicts](#conflicts-g2)).
6. **Headers.** `isValidHeader(attested_header)`. With a non-zero finality branch and a
   finalized slot other than `GENESIS_SLOT`, `isValidHeader(finalized_header)`, and
   `hash_tree_root(finalized.beacon)` is proved by the finality branch at the fork's gindex
   under the attested header's `state_root`; otherwise `finalized_header` is
   `LightClientHeader.empty()`.
7. **Next committee.** If `next_sync_committee_branch` is not all zero,
   `hash_tree_root(next_sync_committee)` is proved at the attested slot's gindex; otherwise
   `next_sync_committee` is `SyncCommittee.empty()`. A committee enters the store only through
   a branch that verified.
8. **Age.** `effNow − slotTime(store.finalized.slot) ≤ MAX_AGE`, against `effNow` before this
   update, which only grows, so a failure here is final; checked again after step 9 with this
   update's attested slot counted.
9. **Signature.** The committee is the store's current one for the store's period, the next
   for the next period; the participants are the keys whose bit is set, in order; the fork
   version is the one at the epoch of `max(signature_slot, 1) − 1`; the domain is
   `compute_domain(DOMAIN_SYNC_COMMITTEE, version, genesis_validators_root)`; the signing root
   is `hash_tree_root(SigningData(hash_tree_root(attested.beacon), domain))`; and
   `FastAggregateVerify(participants, signing root, signature)` holds. A next committee that
   differs from one the store holds for that period is a conflict only once this step
   succeeds; when it fails, the source is faulty for the round.

`signature_slot` is not signed: the signing root covers the attested header and the domain
only. It enters acceptance only through step 3, the period that picks the committee (steps 4
and 9) and the fork version the domain binds (step 9): `validate` gives the same answer for
every `s′ > attested slot` in the same period whose `max(s′, 1) − 1` has the same fork version,
and a change of `signature_slot` changes only `isBetter`'s last tiebreak (25d). So no clock
bound on it is needed: the clock judges age only, through `effNow` on the signed attested slot.

### Processing an update

`Store.process`, the specification's `process_light_client_update` and
`apply_light_client_update`, without the forced update and without the optimistic header:

- The update replaces the period's best update when `isBetter` prefers it (kept for the
  evidence).
- With two thirds signing and a newer finalized header, or a finalized next committee the
  store lacks, the update is applied: the next committee is learned; when the finalized
  header enters the next period, next becomes current, the update's next becomes next; the
  finalized header advances.
- Every verified update's finalized checkpoint and next committee's root are kept for
  `MAX_AGE` ([Conflicts](#conflicts-g2)).
- **The anchor** is the newest attested header signed by two thirds of the committee for its
  signature period (the store's current or next), from any verified update, finalized or not,
  within `MAX_AGE`. Anchors are ordered by (attested slot, first verified): a header at the
  same slot with another root never replaces the anchor, and raises the G9 warning.
- **Without finality** the committees move only when a newer header finalizes, and `validate`
  accepts the store's period and the next only. So new anchors stop once the chain's period
  reaches the finalized header's period + 2: 27 to 55 hours after the last finality, at 12 s
  slots.

`isBetter(new, old)`, in order: a supermajority beats none; below it, more participants; a
relevant next committee (attested and signature in one period) beats none; finality beats
none; sync-committee finality (finalized and attested in one period) beats none; then more
participants; then the older attested slot; then the earlier signature slot. It is a strict
preference (irreflexive and transitive: a lexicographic order on keys computed from each
update), to be proved (25f) and checked by the `update_ranking` vectors.

### Catch-up

The target period is `t = period(max(slotOf(clock), the highest attested slot any source
claims, verified or not))`. When `t` is more than one period ahead of the store, or the next
committee is unknown, the planner asks `updates?start_period=s&count=min(t − s, 14)`, with `s`
the finalized period when the next committee is unknown and the period after it otherwise,
until `t` is reached; updates are verified in order, the evidence is persisted after each
batch, and the routine poll resumes. A source whose claim the returned chain cannot reach is
faulty for the round; the work budget bounds what a lying far-future claim costs.

At each start the request is the same for every `lkd`, whatever its absence:
`start_period = current − 13`, `count = 14`, `current` from the clock. That covers `MAX_AGE`
in about 377 KB of SSZ, or about 0.8 MB of JSON, under netd's 1 MiB HTTP cap
(`crates/netd/src/http.rs:20`). Updates byte-identical to the evidence skip BLS, committees
equal to ones held skip KeyValidate, and an older period's update that differs from the one
held is compared ([Conflicts](#conflicts-g2)).

### Where lkd departs from the specification

- **No forced update.** `process_light_client_store_force_update` treats an attested header as
  finalized after `UPDATE_TIMEOUT` without finality, trading safety for liveness. `lkd` stalls
  and says so. Updates with fewer than two thirds signing are refused before BLS: without a
  forced update or an optimistic header they could never be used.
- **The anchor needs two thirds**, not the optimistic header's more-than-half of the recent
  maximum.
- **Conflicts halt** ([Conflicts](#conflicts-g2)); the specification keeps the first valid
  update.
- **An unknown fork fails closed**: bytes tagged with another fork than the one `Forks` gives
  for the attested slot are refused, and their source is faulty for the round. "Unknown fork"
  is said only when every source that answers, at least two, tags slots beyond the table's
  last fork with a version or digest the table lacks.
- **The clock does not refuse a signed update.** The specification asserts `current_slot ≥
  signature_slot`. `lkd` judges age only, against `effNow`, and says "clock behind" when
  verified data is newer than the clock ([The clock](#the-clock-g6)); a refusal would hide a
  slow clock behind a stall, and the invariance of `validate` in `signature_slot` (25d) shows
  nothing else depends on it.
- **The age bound `MAX_AGE`** holds on every update, anchor and replayed step; the
  specification has none.
- **Several sources** are asked and compared.

### Conflicts (G2)

Two kinds halt the store, each side a verified update signed by two thirds:

1. **Finality**: two finalized checkpoints of one epoch with different roots. The epoch is
   read from `finality_branch[len − floorlog2(gindex)]`, the root's sibling, bound by the
   branch (`branch[0]` for a native branch). A checkpoint's block can sit before its epoch's
   first slot (`altair/light-client/full-node.md:87-90`), so two forks' checkpoints of one
   epoch may sit at different slots; honest committees sign heads whose states finalize one
   checkpoint per epoch unless FFG's safety failed.
2. **Next committee**: two committees for one period. A deep fork across a period boundary is
   one honest way to two of them; halting on it costs liveness only (open decision 15).

**What is compared.** The store keeps, for `MAX_AGE`, the epoch, root and slot of every
finalized checkpoint in a verified update (about 3,150 entries, 126 KB) and every period's
committee root, persisted with the evidence. Comparison runs before the relevance check, under
the work budget, on every update whose signature verifies under a committee the store holds
for its signature period: the current or next one, or a past period's, carried by the
evidence's best update of the period before.

The pair is written to the evidence's conflict block (`PersistConflict`, before anything else
is done), and the store halts until the user takes a new checkpoint. A halted store answers
nothing as proved. Any two sets of 342 out of 512 overlap in at least 172 members (25g states
it), so at least 172 members signed both sides. `Load` halts on a stored conflict only when
both its updates verify (two thirds, and BLS under the committee the replay from the
configured checkpoint reaches for each signature period) and disagree in one of the two kinds;
a block that does not, after a new checkpoint for example, is shown in Settings as history.

Different attested roots at one slot are **not** a conflict: a committee that follows fork
choice across a proposer's equivocation signs both, at different slots. `signature_slot` cannot
tell those slots apart, since no one signs it, so a rule on it could be set off by any source
from two honest updates. The first anchor stays, and the G9 warning is raised.

### The store and the evidence, as built (LC5)

Built on `lc5/work` (2026-10-26): `LkdLc.Forks`, `LkdLc.Store`, `LkdLc.Codec`, `LkdLc.Evidence`,
their wiring into `LkdLc.Lc` and `LkdLc.Ffi`, and `LkdLcDev` (the minimal preset's decoders and
the development table); theorems in `LkdProofs.Lc.{Forks, Store, Evidence}` (25d to 25i, 25n);
`lake exe lkd-lc-store-test` ([Testing](#testing)). LC6's planner fetches beacon data and the
anchor drives `Account` ([below](#the-planner-and-anchored-reads-as-built-lc6)); LC5's
`Lc.receiveBootstrap` and `Lc.receiveUpdate` stay as the store's entry points for tests (only
`LkdTests.Store.Own` calls `receiveUpdate`); `step` takes beacon objects through LC6's inbox
(`Lc.ingest`) under the work budget, which follows them.

**Objects.** The store runs on normalized objects (`Store.Header`, `Update`, `Bootstrap`) that
`Codec` builds from the SSZ of the fork the tag names: `Codec.mainnet` from `LkdLc.Ssz`'s
decoders, `Dev.codec minimalPreset` from `LkdLcDev`'s. A header keeps its beacon header, what
its execution branch proves (an Electra or Fulu payload header, or a Gloas
`execution_block_hash`) and the branch; `isValidHeader` chooses the gindex by the header's own
slot (25, 2856, or 812 before Gloas in a Gloas container). Headers stay in the form they were
validated in: every check, and `get_lc_execution_root`, give the same answer for an Electra
header and its upgrade, so the vectors' `upgrade_store` changes nothing. `Store.elTag` is
`Parent` exactly from `GLOAS_FORK_EPOCH` on.

**Acceptance** (`Store.receive`): halted refuses; `formOk` (two thirds, `signature_slot >
attested ≥ finalized`, the attested header valid, the finality and next-committee branches, or
empty fields); a committee for the signature period: current, next (then the update may be
accepted), or a past one, kept with its keys for 16 periods (then it is only compared); the age
bound; BLS; then `afterBls`: the attested slot counted in `effNow`, the comparison (a conflict halts
the store, whatever follows), the update's checkpoint and next committee's root kept, and, for
the current or next committee, the age bound again, relevance and `process`. A next committee's
keys pass KeyValidate when it becomes the store's next (`learn`), and an update whose committee
has a key KeyValidate refuses is refused (`badKeys`): stricter than the specification, which
validates keys only at the bootstrap and would fail every later signature. `isBetter` is the
lexicographic order on `Store.rank`; the specification's text, transcribed in the tests, agrees
with it on every pair of the `update_ranking` vectors. `best` is kept, as the specification keeps
it, and not persisted. `Store.verifyHistorical` checks an old update under any committee the store
holds without changing it (for LC6's snapshot re-checks, G19).

**What is kept for conflicts, and what it departs from.** The store keeps, in memory, each
finalized checkpoint (epoch, root, slot) of every update whose signature verified, with a witness
(the attested header, the aggregate, the signature slot, the finality branch and its leaf), at
most 4,096, those older than `MAX_AGE` against `effNow` dropped; and each period's committee root
with the witness of the update that brought it (the bootstrap's own committee without one), at
most 32 periods. They are **not persisted**: a witness each for 3,150 epochs does not fit a 1 MiB
copy, and entries without witnesses would be trust the evidence cannot carry (an entry read back
unverified could halt the store). `Load` rebuilds them from the updates it replays. The conflict
block holds the two witnesses, not two full updates: what verifies a side again is the signature
over the attested header and the branch from the leaf, which a witness carries.

**The evidence payload** (`Evidence.encodePayload`): version `02` ‖ the checkpoint (32) ‖ the
bootstrap's fork (1: `0` Electra, `1` Fulu, `2` Gloas) ‖ its SSZ after a 4-byte length ‖ the
number of updates (2) ‖ each update's fork (1), kind (1: `0` update, `1` finality, `2`
optimistic) and SSZ after a 4-byte length ‖ the grid section: `00`, or `01` ‖ the grid
checkpoint's root (32) ‖ the update that proved it, as an item ‖ its bootstrap's fork (1) and SSZ
after a 4-byte length ([Refresh](#refresh), added in LC6; version `01`, LC5's, had no grid
section and is no longer read: its copies give way to the network bootstrap). The updates are the one that set each next committee
the store learned, one per period, in order (at most 32), then the latest update the store
accepted; replayed from the bootstrap, each committee-setting update moves the store into the
period whose committee it set, and the last brings back the finalized header and the anchor. A
copy is `LKDLCCP1` ‖ sequence (8) ‖ length (4) ‖ SHA-256 of the payload ‖ payload; the conflict
block is `LKDLCCF1` ‖ sequence ‖ length ‖ SHA-256 ‖ the conflict (kind, the held witness or none,
the new one). The grid checkpoint is [Refresh](#refresh)'s, as built.

**Load and Persist.** `Load` reads the conflict block (and emits `ClearConflict` when its
sequence is the configuration's eighth field), then checks the copies whose framing and SHA-256
hold and whose payload names the configured checkpoint, newest sequence first: at each `Tick`,
the bootstrap alone (its committee's KeyValidate), or up to four updates and none after one whose
committee's keys were validated; a copy whose bootstrap or any update is refused gives way to the
other, then to none; once a copy's updates are replayed, its grid checkpoint is checked in a step
of its own (`Evidence.checkGrid`) and kept only when it holds, the copy loading either way. A
loaded store halts on the stored conflict only when both its witnesses verify under the loaded
store's committees and disagree (`Store.Conflict.stands`). After a
committee is learned, or an epoch after the last write, a `Tick` persists the payload to the copy
not last loaded or written, at the next sequence (`Evidence.Copies`, generic over the payload).

### The planner and anchored reads, as built (LC6)

Built on `lc6/core` (2026-10-26): `LkdLc.Plan`, `LkdLc.Anchor`, `LkdLc.Facts`, their wiring into
`LkdLc.Lc`, `LkdLcDev.Ffi`; theorems in `LkdProofs.Lc.{Anchor, Plan, Core, Evidence, Anchored}`
(25j, 25k, 25p, 25r's LC6 part); `lake exe lkd-lc-plan-test` and the fake beacon,
`lkd-e2e-beacon-gen` ([Testing](#testing), `proofs/tests/README.md`).

**`Account(a)` with a light client** (`Lc.accountLight`): `Error(NotAnchored)`, code 7, unless the
phase is Anchored (`anchorNow`), so no store yet, syncing, checking evidence, halted, too old,
clock behind and unknown fork all answer it, and the client falls back to one endpoint's path,
yellow (the decision of 2026-10-26: clock behind included, so [Failure states](#failure-states)'
"Clock behind" row shows yellow values, today's check). At the anchor `L`: the anchored answer
(kind 2) once the planner holds the EL header for `L`'s EL hash and the proof for `a`, both checked
again as it is answered (`anchoredAnswer`: `Anchor.bind`, `Facts.account`); the error the read
ended with (`Refused`, `Unreachable`) for 3 s; otherwise `Pending(500)`, the read wanted and the
planner run at once. Reads are kept per address and anchor EL hash: when the anchor moves, the
next ask fetches again. The anchored fields: `L`'s slot and beacon root, the finalized EL number
(the finalized payload header's, or a Gloas-form finalized header's EL header's once fetched and
bound by 25j, `0` until then), the age (`now − slotTime(slot)`, `0` when the clock is behind), not
final, and the tag. `AccountFinal` stayed `Unsupported` until LC9, which answers it at the
finalized header ([`lkd-lc` (LC9)](#lkd-lc-lc9), D40). Without a light client, LC1's endpoint path.

**The planner** (`Plan.pump`, run on every `Tick`, every response and failure of its own fetches,
and every `Account`), at most 2 new fetches an input and 2 in flight (`perStep`, `maxJobs`; 8 and
16 until D43, LC9: netd serves one request at a time, so more only queued there, outside this
order), each under a fresh tag, in this order:

1. **Reads**: `ElHeader(attempt, h)` for the anchor's EL hash while a read waits for it (and the
   Gloas-form finalized header's), then `ElProof(attempt, h, a)` for each waiting read, newest
   first. `attempt` counts the asks after a refusal or a failure (netd picks the endpoint from it);
   after 3 the read ends with `Refused` or `Unreachable`, told for 3 s, then asked again from 0.
   A header is kept only when `Anchor.bind` keeps it; a proof only when `Facts.account` reads an
   account from it equal to the endpoint's word.
2. **Bootstrap**: `Bootstrap(source, checkpoint)` while there is no store and no evidence check,
   one at a time, sources in rotation; with a store, the wanted grid checkpoint's, at most four
   times for one root ([Refresh](#refresh)).
3. **Catch-up**: first the uniform request (`start = current − 13`, `count = 14`, clamped to the
   periods that exist), then, while the next committee is unknown or the target period (the
   clock's, or the highest attested slot a source claimed) is more than one past the store's,
   `Updates(source, s, min(max(t − s, 1), 14))`, at most every 12 s; claims are dropped when a
   catch-up is sent.
4. **Polls**, skipped while a read waits: `FinalityUpdate` from every available source once an
   epoch (which also clears last round's faulty marks), and from one source in rotation once a
   slot, a third of a slot in (a quarter under Gloas).

A beacon source that fails waits 1 s doubled per failure in a row, at most 60 s; one whose bytes
do not decode as the fork it named, or whose update is malformed or fails BLS, is faulty until
the next epoch's round; one naming a fork the table lacks, or answered `NotSsz`, says "unknown
fork", and the phase is Unknown fork when every source that answered, at least two, says so.
`OptimisticUpdate` and the "a source an epoch ahead" trigger of [Several sources,
compared](#several-sources-compared-g1-g3) are not asked yet. Pages are pulled with `FetchPage`,
at most 8 MiB and 192 pages a response. Beacon objects wait in an inbox of 32; each `Tick` first
verifies at most four (`Lc.ingest`: a bootstrap alone, or updates, stopping after one whose
committee's keys were validated or one that halted the store), before the evidence is checked or
persisted, so a conflict block is the step's first effect; then the evidence (`tickLight`), the
planner's fetches timed out (after 30 s in LC6; since D13, `Plan.jobMs`, 57 s, and `Lc.fetchMs`
with it, and `Plan.bodyJobMs`, 74 s, for G12's bodies; since D43, 140 s and 155 s, backstops
above the shell's two phases; a paged fetch counted from its last page), and the planner.
`BlockRoot` is never asked by `step`: it
is `--propose`'s, which asks it with `Plan.proposeAsks`' requests and takes the root by
`Plan.proposeRoot` (`Plan.proposeAgreed`'s rule), both through `LkdLc.Ffi`'s exports ([the
one-shots, as integrated](#the-first-checkpoint)).

**What is proved, and what is tested.** Proved: 25j (`bind_spec`), 25k (`account_spec`), 25p
(`anchored_sound`, `step_notAnchored`, `step_endpoint_answers`), the planner's bounds and the state's
(`pump_spec`, `Plan.Bounded` in `Inv`, `step_good`), stores through the inbox (`run_reaches`), the
conflict block first, and only for an update of the inbox that conflicted, the halted store's
conflict framed with the next sequence (`step_persistConflict`). Tested (`lkd-lc-plan-test`, 58 checks in LC6,
102 with G19's snapshots (`LkdTests.Lc6.Snapshot`), the refresh's scenario and `--propose`'s
exports): the order,
liveness and backoff; own-hash and Gloas parent-hash anchoring with recorded EL data; tampering;
disagreeing, faulty and `NotSsz` sources; catch-up over periods; a chain generated again as it
grows past an epoch's first slot (the integration's fix to the generator, which had named two
roots for that epoch), unhalted. End to end, the 13 `lc-*` scenarios ([Testing](#testing)).

**The development start** (`dev-insecure` only): `lkd-lc --dev-genesis <s> --dev-gvr <root>
[--dev-gloas <epoch>]` calls `lkd_lc_init_dev` with the 57-byte configuration and 48 more bytes,
the genesis time (8), the genesis validators root (32) and the Gloas epoch (8, `2⁶⁴ − 1` for
none): the development table for the fake beacon, the minimal preset's codec, whatever the chain
id. `lkd-lc-core`'s `dev` feature links `liblkdlcdev.a` and starts the runtime with `LkdLcDev`'s
initializer.

## Cryptography in Lean

### What is computed

- **SHA-256** for every `hash_tree_root` and branch.
- **SSZ**: decoding with offsets (the Electra containers are variable-size through
  `extra_data`), merkleization of the light-client containers (`ProgressiveContainer` for
  Gloas), `hash_tree_root` of a `SyncCommittee`, normalized branches.
- **BLS12-381**, verification only, on public data, so constant time is not required.
  KeyValidate of each committee key, once per committee: decompress (48 bytes, ZCash's flags),
  on `E: y² = x³ + 4`, not the identity, and `[r]P = O`. The aggregate: the sum of the
  participants' keys (not the committee's `aggregate_pubkey` minus the absent, helios's
  shortcut, which rests on an unchecked equation); an identity aggregate is refused, as
  CoreVerify's KeyValidate of the key does. The signature: decompress (96 bytes) on the twist
  `E': y² = x³ + 4(1 + i)` and `[r]Q = O`; an identity signature is refused before the pairing
  (under a non-identity aggregate it never verifies). `hash_to_G2` of the signing root (RFC
  9380, `BLS12381G2_XMD:SHA-256_SSWU_RO_` with Ethereum's DST): `expand_message_xmd` with
  SHA-256, two `Fp2` elements, simplified SWU on the 3-isogenous curve (it branches on Euler's
  criterion and refuses when no root is found, never falling back to zero), the 3-isogeny (a
  zero denominator gives the identity, as RFC 9380 §6.6.3 requires, where EthLib's code divided
  by zero; its vendored copy is corrected), `clear_cofactor` as `[h_eff]P` (open decision 12,
  built so in LC4a), a hash that is the identity refused. Then one Miller loop over two affine
  pairs in CoreVerify's arrangement, `e(g1, sig) · e(−agg, H(m))`, as EthLib's, and one final
  exponentiation, which must give one. The tower is `Fp2 = Fp[i]/(i² + 1)`, `Fp6`, `Fp12`, with
  the curve parameter `x = −0xd201000000010000`.

### Sources

From the reuse matrix of 2026-10-24 (`scratch-lc/research/reuse.md`, rows C1 to C13 and rules D1
to D19, which this design follows). DEPEND is a Lake dependency of `LkdProofs`; VENDOR-SPEC a
copy into `LkdProofs` with an equality to our code; VENDOR-RUNTIME a copy into runtime Lean,
rewritten to the rules; LEARN reads or runs it as an oracle and copies nothing.

| Source (pin) | Licence | Decision | Use |
|---|---|---|---|
| The benchmark of 2026-10-24 (2,148 lines, Lean 4.35) | written for lkd | Runtime | The BLS fast layer, moved into `LkdLc.Bls` with a provenance note (done, LC4a). Its SHA-256 was kept as `LkdLc.Bls.Sha256` until LC3's `LkdBase.Sha256` replaced it, and is gone (D1), its `CheckRules.lean` not at all (D13); its py_ecc-generated isogeny constants are checked by `decide` against EthLib's (`LkdProofs.Lc.Bls.Provenance`) and by the test executable against RFC 9380 E.3's text and py_ecc 8.0.0 (C4c) |
| ethereum/ssz-specs `lean/` (`3394318c`) | MIT, © 2025 Ethereum Foundation | DEPEND if it builds unmodified on 4.35, after a source review (no `#eval`, `run_cmd`, `initialize`, `extern`, IO macros or Lake scripts), its modules imported one by one, never `Ssz`; else VENDOR-SPEC into `LkdProofs/Vendor/SszSpecs/`. **The gate (LC3, 2026-10-26)**: the review found none of those in the planned modules' closure (its one elaboration-time command, `audit_ssz`, is in `Ssz/Proofs/Audit.lean`, outside it); built one by one in a scratch package on 4.35, the modules fail only because its lakefile's `warningAsError` turns 4.35's deprecation of `if_pos`, `if_neg`, `if_true`, `if_false` and `dif_neg` (some 190 uses) into errors, and all build in 17 s with warnings allowed. So it is VENDOR-SPEC: the 37 modules LC3's theorems need, its `LICENSE`, a header per file; repairs: imports renamed, its SHA-256 import pointed at `LkdBase.Sha256`, `private` dropped from `Serialize`'s two `@[csimp]` so `Audit.lean` lists them | The SSZ specification and its proofs: canonicality (`Proofs/Codec/Canonicality.lean:65,72`), `verifyMerkleProof_binding` (`Proofs/Merkle/Authentication.lean:141`), `getGeneralizedIndex` (`Type/Paths.lean:191`). Its `Ssz/Hash/Sha256.lean` is vendored as `LkdBase.Sha256` (VENDOR-RUNTIME: `get!` to `getD`), the one copy: the vendored specification imports it, keeping its namespace, so no `getD` lemma is needed. Its codec is not run: dynamic `Desc`/`Value` universe, `!`, non-tail recursion (C2b) |
| ethereum/EthLib (`57af539e`; its Lean files are cryptography-specs `40db10a`'s) | CC0-1.0 | VENDOR-SPEC (C4b, C4c, C4g, C4h): the readable layer is a specification in `LkdProofs`, since its equalities with the fast layer need Mathlib; this corrects reuse C4a's `@[csimp]` route (open decision 21) | Rewritten to be total (`partial` to fuel, `!` to `getD`, panics to `Except`, `while` to bounded `for`), its isogeny constants made public (done, LC4a: `LkdProofs/Vendor/EthLib/Bls`, each file's header listing its changes; semantic ones: `clearCofactor` is `[h_eff]P`, EthLib's G.3 kept as `clearCofactorG3`; SSWU's panic is the error `sswuNoRoot`; the isogeny's zero denominators give the identity; its C exports, `runBls` and `panicWith` left out; its SHA-256 is the runtime's `Ssz.Sha256.hash`, EthLib's own `Bls/Sha256.lean` not vendored, so that `Spec.Sha256` stays the one SHA-256 specification (D1)); the certificate data for p; `G1Group` and `G1Order` ported to Mathlib 4.35 over `[Field F]` with a = 0, for G1, G2 and later secp256k1 (D5); its Fp square-root proof; `ethFastAggregateVerify` as 25c's target. Its own `PowMod` is not taken (D7) |
| Mathlib v4.35.0 (`56a00585`) | Apache-2.0 | DEPEND, proofs only | `QuadraticAlgebra` for `Fp2`, a `Field` once `Fintype` and `CharP` are added (no third hand-rolled Fp2, D6); `X_pow_sub_C_irreducible_of_prime` for `Fp6`, with `Fp12` as `QuadraticAlgebra Fp6 v 0` (C4f; not tried end to end); `lucas_primality` with `decide +kernel` over `Nat.powMod` for p and r (C4d; r done this way in 1.25 to 1.5 s); the Weierstrass Jacobian; Euler's criterion (C5c) |
| Lean core v4.35.0 (`eb6cafb`) | Apache-2.0 | DEPEND | `Nat.powMod` (GMP's `mpz_powm`, a core builtin; `powMod_def`), at runtime and in proofs (C5a) |
| VCVio (`88efe971` with 4.35) | Apache-2.0 | DEPEND | `VCVio.Algorithms.Sha2` becomes `Spec.Sha256` in place of the vendored `Vendor/VCVio/Sha2.lean` and `Sha512.lean` (D19, LC0); `VCVio.Algorithms.Keccak` stays `LkdCore.Keccak`'s specification. Its Merkle binding is LEARN only (C3, D11) |
| CompPoly (`1cb8f5c`) | Apache-2.0 | DEPEND only if C4f stalls | `irreducible_X_pow_sub_C` handles `X⁶ − ξ`; its Montgomery code is LEARN (C5b) |
| daira/CompElliptic (`2c044403`) | Apache-2.0 OR MIT per its README:159-161 only, no LICENSE file | LEARN | Its SSWU, 3-isogeny and Tonelli–Shanks proofs are N7's subject, which the user's decision 3 rules out; this overrides reuse C4i and its follow-up 8 (open decision 21) |
| alexanderlhicks/leanerSTFSpec (`87754c75`) | Apache-2.0 OR MIT, taken under MIT | LEARN only | Its `patricialize` and `root` (`STFSpec/Commit/Root.lean:1169,1479`) are not vendored (LC8): they bring their own RLP encoder (a second RLP specification, D3, D16), packed nibbles and `Std` maps, and only structural laws; the trie's specification is `Spec.Mpt.Trie`, the Yellow Paper's (`proof/mpt-trie`). Its `ByteArray` RLP decoder is LEARN (C7b) |
| skbaek/jaune (`3e078b3a`), Verified-zkEVM/evm-asm (`7e65e4d`) | MIT | LEARN | Oracles for trie roots, receipts, bloom and transaction types (C8b, C9) |
| etheorem's `EthCLLib` (`54a3683`) | LGPL-3.0-only | LEARN | A differential oracle for 25d (`computeDomain`, `computeSigningRoot`, `processSyncAggregate`), run out of the tree; no code copied (C10a) |
| pure-algebra/lean4-hash (`ab7eda43`) | MIT | Alternative only | A second runtime SHA-256 candidate, if ssz-specs' fails `CheckCore` (C1b) |
| `LkdCore.Keccak`, `LkdCore.Rlp` | in tree | KEEP, in `LkdBase` | Faster only through `@[csimp]` (C6, C7a) |
| consensus-specs v1.7.0-beta.4 vectors; RFC 9380 J.10.1; EthLib's `tests/cryptography/bls`; ethereum/bls12-381-tests v0.1.2 (`89ff3a86`, added in LC4a) | CC0-1.0 (its `LICENSE`); IETF; CC0-1.0; CC0-1.0 | Vectors | A committed, pre-decompressed subset, hashed (BLS: `proofs/tests/LkdTests/Bls/Vectors.lean`, written by `scripts/bls-vectors.py` with each source file's SHA-256) |

Every vendored directory carries its upstream `LICENSE` file and reuse §4's attribution header.
A repository without a licence file is never copied (reuse §4's list, and CompElliptic).

### Speed

Measured on 2026-10-24, AMD Ryzen 9 9955HX3D, Lean 4.35.0, `lake build` (clang 23.1.0, `-O3`),
GMP 6.3.0 linked statically, single-threaded; each figure the best of three interleaved runs.
Peak memory 11 MiB.

| Operation | Time |
|---|---|
| Fp multiplication (`a * b % P` on `Nat`) | 131.8 ns |
| Fp inverse (`Nat.powMod`) | 20.3 µs |
| Fp12 multiplication | 18.97 µs |
| G2 doubling / addition | 5.01 / 9.11 µs |
| Two-pair pairing product, one final exponentiation | 7.29 ms |
| `hash_to_G2` (with G.3's `clear_cofactor`, 802 µs) | 1.14 ms |
| G1 decompression | 25.5 µs |
| G1 subgroup check: Scott's test / `[r]P` | 255 / 829 µs |
| G2 decompression; subgroup check by ψ | 73.4 µs; 385 µs |
| Aggregating 512 keys | 1.21 ms |
| `hash_tree_root(SyncCommittee)` | 0.90 ms |
| SHA-256 of 1 MiB (the bench's; ssz-specs', `LkdBase.Sha256`, measured 2026-10-26 on the same machine, under another agent's build: 5.59 ms, best of five runs of 20) | 5.90 ms |
| **An update** (aggregate, `hash_to_G2`, signature checks, pairing, about 150 SHA-256 compressions estimated) | **about 10.2 ms**; 11.1 ms with a next committee's root |
| **A committee**: 512 decompressions and KeyValidates | 0.145 s with Scott's test; **about 0.44 s with `[r]P`** |

**As built in LC4a** (`LkdLc.Bls`, measured on 2026-10-26 by `lake exe lkd-bls-test` on the
same machine, shared with other work, pinned to one core with `taskset`; each the best of
four runs of the program, each the best of nine passes, a committee's of two; the four
runs' updates took 17.0 to 17.6 ms):

| Operation | Time |
|---|---|
| **An update**: `fastAggregateVerify` over 512 keys (aggregate, `hash_to_G2`, the signature's decompression and `[r]Q`, the two-pair check) | **17.0 ms** |
| of which: aggregating 512 keys, to affine | 1.20 ms |
| `hash_to_G2` with `clear_cofactor` as `[h_eff]P` / `[h_eff]P` alone | 5.98 ms / 5.65 ms |
| The signature: decompression and `[r]Q` | 2.41 ms |
| The two-pair pairing check | 7.30 ms |
| **A committee**: 512 decompressions and KeyValidates with `[r]P` | **0.41 s** |
| For reference, EthLib's readable layer: `eth_fast_aggregate_verify` of one key | 248 ms |

The update meets LC4a's 20 ms with `[h_eff]P` (open decision 12) and without Scott's test or a
window for the scalar multiplications; the SHA-256 of the branches and header roots, about
0.13 ms (*estimate*), is LC3's and not in it.

v1 uses `[r]P` and `[r]Q`. Before LC4a, `[r]Q` for the signature was estimated at about 2.5 ms
from the G2 figures (254 doublings and 133 additions), an update at about 12 ms, or about 17 ms
with `[h_eff]P` (`h_eff` has 636 bits, 305 set: about 5.1 ms more); LC4a measured 2.41 ms with
the decompression, and 17.0 ms. Replaying the evidence costs about 0.44 s per committee it
holds; it spans at most `MAX_AGE` from the checkpoint, so at most about 13 committees: about
5.7 s on this machine, 12 to 23 s on a laptop two to four times slower, doubled when the newer copy
fails, and about 3.5 s here when the checkpoint is refreshed after 7 days. It is checked a
committee per tick, so `Status` answers meanwhile. `xs[i]?.getD 0` costs nothing against
`xs[i]!` (SHA-256 at 5.88 against 6.43 ms per MiB), and `for` loops and structural fuel cost
nothing measurable. Lean core has no 64×64→128 multiplication, so a generated six-limb
Montgomery multiplication reaches 70.5 ns, 1.87 times GMP's; a Montgomery tower is not built,
and not needed. lean-native gives no speed-up on this code ([Tooling](#tooling)).

### Proved, checked by vectors, trusted

| | Proved, or to be (`LkdProofs/Lc`) | Checked by vectors and differential tests | Trusted |
|---|---|---|---|
| SHA-256 | `LkdBase.Sha256.hash` (ssz-specs' `Ssz.Sha256.hash`, the one copy) equals `Spec.Sha256.sha256`, VCVio's FIPS 180-4 transcription, on every message: proved directly (`Lc.Sha256.hash_eq_spec`, LC3), not through `hash_refines` | NIST vectors | |
| SSZ | Each `hash_tree_root` equals ssz-specs' at its `Desc`, and every decoded value fits its type; a normalized branch is binding (`verifyMerkleProof_binding` on the suffix, `Spec.Ssz.collision` computed as `Spec.Mpt.collision` is); the gindex table by `getGeneralizedIndex`; the `/updates` framing canonical (all LC3) | `ssz_static`, `single_merkle_proof`; each decoder against `deserialize` (not proved in LC3) | |
| Fields | Proved (LC4b, `LkdProofs.Lc.Bls.{Primes,Fp,Fp2,Tower}`): p and r prime (Lucas, `lucas_primality` over `ZMod` powers, no `native_decide`), gcd(3, r) = 1; the runtime's `Fp` arithmetic on `Nat`s below p is `ZMod p`'s and, on its values, EthLib's `Fin p` operations, Fermat inverse and square root included; `fsqrt?` finds a root exactly of the squares, `fIsSquare` is Euler's criterion; `Fp2` is Mathlib's `QuadraticAlgebra (ZMod p) (−1) 0`, a field, with the runtime's and EthLib's products, inverses, `mulXi` and conjugate its own, `Fp2.sqrt?` sound and complete (the complex method, through Euler's criterion on the norm), `Fp2.isSquare` true exactly on the squares; ξ = 1 + u neither a square nor a cube; `Fp6` (`AdjoinRoot` of X³ − ξ, irreducible by Mathlib's Kummer criterion) and `Fp12` (`QuadraticAlgebra Fp6 v 0`, v not a square by its norm ξ) fields of p⁶ and p¹² elements (C4f, done), with the runtime's and EthLib's tower operations theirs; EthLib's `Fp2.sqrt` is the runtime's `Fp2.sqrt?` (LC4b's rest, `sqrt?_ofEth`), so sound and complete too | The Frobenius and the cyclotomic squaring (only the final exponentiation uses them) | |
| Curves | Proved (LC4b, `LkdProofs.Lc.Bls.{Jacobian,Curves,Decompress}`): one a = 0 Jacobian development over any field (D5, ported from EthLib's `G1Group`): dbl-2009-l, add-2007-bl, madd-2007-bl and the top-bit double-and-add are the group law; the runtime's G1 and G2 formulas are its; `onCurve` is the curve's equation, which makes a point nonsingular; `isInf`, `toAffine?` and `[r]P = O` mean what they say; the generators are on their curves with order r (`[r]G = O` run by the kernel); a decoded point is reduced, on its curve and not the identity, and decoding is unique (two encodings of one point are the same bytes), KeyValidate and the signature's checks add `[r]P = O`, the identity's encodings are refused. LC4b's rest (`LkdProofs.Lc.Bls.{Roundtrip,EthCurves}`): decoding is canonical (the one encoding accepted is `compress p`) and complete (every reduced point's compression decodes back to it; with `[r]P = O`, KeyValidate and the signature's checks accept it), by `natBe` and `beNat` read as base 256 and the sign flag fixing the root, no `native_decide`; EthLib's own G1 and G2 formulas, its bottom-up `mulNat` included, are the group law too | | |
| `hash_to_G2` | Proved (LC4b's rest, `LkdProofs.Lc.Bls.{HashCurve,HashEth}`): on every input the runtime's `expand_message_xmd`, `hash_to_field`, SSWU (its refusal exactly EthLib's error), the 3-isogeny and `[h_eff]` equal EthLib's rewritten `HashToCurve`, both hashing with `Ssz.Sha256.hash`, compared as terms (only its 32-byte size used), so `hashToG2?` is EthLib's `hashToG2` read as an affine point, `none` exactly when EthLib errs or returns the identity (`hashToG2?_eq_eth`). What `hash_to_G2` returns is a reduced point of E′ (`hashOnCurve`, so `HashOnCurve` is no longer a hypothesis): SSWU's y is a checked root of g(x), RFC 9380 E.3's isogeny maps E′′ to E′ (the degree-15 polynomial g·y_num²·x_den³ − x_num³·y_den² − b′·x_den³·y_den² has zero coefficients, computed from the constants by the kernel), and the group law and `[h_eff]` keep the point there. The constants equal EthLib's (`Provenance`). The kernel cannot check `f x = body` for these definitions (it unfolds the body's `match` first and evaluates its discriminant), so they are unfolded through `f = fun x => body` (`value_eq`) | G.3, if decision 12 keeps it: EthLib's `clearCofactorG3` against `[h_eff]` (vectors) | |
| Pairing | Proved (LC4b, `LkdProofs.Lc.Bls.{FinalExp,Fav}`): the cube lemma, `(f^((p¹²−1)/r))³ = 1 ↔ f^((p¹²−1)/r) = 1` in `𝔽_{p¹²}` (gcd(3, r) = 1, r ∣ p¹² − 1, Fermat), and EthLib's `finalExponentiation` is that power, so given H_vec's equation for a check (`FinalExpCube`) the runtime's check is EthLib's (`finalExp_isOne_iff`); FastAggregateVerify sums the participants' keys (`aggregate?_spec`) and, for any e additive in its first argument on G1 × G2 given `PairingCheckIs e` on G1 × G2 and `HashInG2` (and `HashOnCurve`, proved since: `fastAggregateVerify_iff_pairing`), is true exactly when Σpkᵢ ≠ O, the signature is a point σ of its checks, `hash_to_G2(msg)` a point H, and e(g₁, σ) = e(Σpkᵢ, H) (`fastAggregateVerify_iff`, over the keys' bytes `fastAggregateVerifyBytes_iff`); the pairing's laws are hypotheses in `Spec.Bn254`'s shape, never an axiom (D18). LC4b's rest (`LkdProofs.Lc.Bls.FavEth`): given that cube equation for each check (`MillerLoopsCube`), wherever EthLib's `hash_to_G2(msg)` is not the identity and the signature is not the identity's encoding, `fastAggregateVerifyBytes` is EthLib's `fastAggregateVerify` on every input (`fastAggregateVerifyBytes_eq_eth`: EthLib's decoders, KeyValidate, `G1.compress`, key loop and naive `pairingCheck` related to the runtime's); with the identity's encoding, EthLib accepts exactly when e(Σpkᵢ, H(m)) = 1, the runtime refuses (`fastAggregateVerify_eth_identitySig`) | That `finalExp (millerLoop ps)` is the cube of EthLib's naive `finalExponentiation` of its `pairingCheck` accumulator over the same pairs (`FinalExpCube`, `MillerLoopsCube`), that the check computes a bilinear, non-degenerate e on G1 × G2 (`PairingCheckIs`), and that `[h_eff]` lands in G2 (`HashInG2`), all H_vec; bilinearity and non-degeneracy (N7), and `[h_eff]` landing in G2, which decide the identity-signature case | |
| Everything | | | BLS unforgeability (H_bls); Lean's compiler and runtime (H_rt) |

The runtime rules (no panic, no recursion growing with the input) are checked by `CheckCore`
(rules 1 to 4, and that every builtin-abort site is in `proofs/ABORTS.allow`), review (recursion
depth, each site's note) and fuzzing; they are not theorems. The `Fp6` and `Fp12` field proofs
did not stall (LC4b), so the check keeps its equality with EthLib's naive check, given H_vec. The
benchmark's own checks (35 self-tests, and agreement with py_ecc 8.0.0 on the pairing up to
conjugation, compressed points, `hash_tree_root`, SHA-256 and `hash_to_G2`) pass. Since LC4a,
`lake exe lkd-bls-test` (`proofs/tests`, [Testing](#testing)) runs every BLS vector, 147 checks,
on both `LkdLc.Bls` and EthLib's vendored code, and they pass on both: the consensus-spec and
EthLib BLS vectors, bls12-381-tests', RFC 9380's J.10.1 (`u`, `Q0`, `Q1` and `P`), SHA-256's
examples; with the self-tests, the constants' provenance, mutated signatures, keys and messages
refused, and the two layers compared off the vectors, the cube included:
`finalExp (millerLoop ps)` equals the cube of EthLib's naive `finalExponentiation` of its
accumulator, on pairs whose product is one and pairs whose product is not.

## Anchoring execution reads

### The EL header, by hash (G7 to G9)

Fetched by `eth_getBlockByHash(h, false)` on the `Head` circuit; netd rebuilds the RLP
(untrusted). The checks follow the tag of the header that names `h` ([Objects](#objects)):

| Tag | The hash | Checked |
|---|---|---|
| `Own`, an `electra` header (mainnet today) | `block_hash` of the payload header proved at 25 under `body_root` | `keccak(rlp) = h`. `execMatches`: state root, number, gas limit, gas used, base fee and receipts root equal the payload header's. `timestamp = slotTime(slot)/1000`. `parentBeaconBlockRoot = parent_root` (EIP-4788) |
| `Own`, a pre-Gloas header upgraded into a Gloas container | `execution_block_hash` at 812 | `keccak(rlp) = h`, the timestamp and `parentBeaconBlockRoot`; there are no payload fields, and the Keccak binding makes `execMatches` redundant |
| `Parent`, a Gloas header (Sepolia since 2026-10-06) | `execution_block_hash` at 2856: the parent payload | `keccak(rlp) = h`, and by the header's own EL fork, from its timestamp: an Amsterdam header (23 fields) has `slotNumber < slot` and `timestamp = slotTime(slotNumber)/1000` (`gloas/fork-choice.md:709-711`); a pre-Amsterdam parent, which the first Gloas blocks build on (`gloas/fork.md:176`), has a timestamp before the Gloas fork's and equal to `slotTime(k)/1000` for some `k < slot` |

The Amsterdam header adds `blockAccessListHash` (EIP-7928) and then `slotNumber` (EIP-7843)
after `requestsHash` (go-ethereum `core/types/block.go:103-107`); 14b already reads 23 fields,
and is restated to read fields 4, 5, 19 and 22 as well. The payload header's
`transactions_root` is an SSZ root, not the EL trie's, so it is not compared. Under Gloas the
anchored EL block lags the head by at least two slots, and the attested slot's own payload is
never authenticated (it may be withheld).

Every fact names its block number and hash, the number of signers, the finalized EL block's
number and its age. **Final** means proved at the finalized EL block itself, asked at its hash
(`AccountFinal`), never inferred by walking ancestry; it is asked for G11's "settled, final"
and for the received-funds notice ("received, final at block N"), at most once an epoch per
address. **Reorgs (G9)**: a fact at `(N, h)` is withdrawn with a warning, and proved again,
when a later anchor shows another hash at `N`, by an EIP-2935 proof (`History(N)`, keyed by the
number only, on `Shared` with the pin and pool batches whose blocks it checks: LC9's D38), or when
an anchored header's own EL block has number `N` and another hash.

### Every ETH balance (G10)

The UI asks `Account(a)`. `lkd-lc` fetches `eth_getProof(a, [], {"blockHash": h})` (EIP-1898)
on the `Account(a)` circuit, from the one endpoint kept for that address (open decision 11),
and caches it per address and anchor; an account proof is about 3.7 to 3.9 KB. It replaces
every `eth_getBalance` the wallet makes.

**As built (LC2, then on the quorum path; one endpoint's since 2026-10-28).** netproto's
`ProvedAccounts` (`0x1f`, page `0x96`; `0x93` until master's `PoolLogs` took it): one head a refresh
(`reads::head`: one endpoint's, the first that answers, the next one's when it fails, or your node's
own), then one `eth_getProof(a, [], N)` per address on its own `Account(a)` circuit at that head,
each checked by netd under that head's state root before it is handed on (`reads::account`), paged
within 64 KiB frames: a page ends once less than 8 KiB of its frame is left or 6 s have passed, at
least one address answered, and the UI asks the rest naming the head it checked (its number and
state root), so netd, serving one request at a time, answers the UI's others in between. An address
no prover proves is answered with why. The UI checks the head and every proof itself
(`lkd_ui::proved`: `check_head` is `header::verify` against the header's own Keccak-256,
`check_account` `mpt::account`), so one refresh proves every balance at one block. Where an
address's proof fails, or no head verifies, its balance is the node's word (`eth_getBalance`),
labelled with why (`lkd_ui::proved::EthBalance::Word`); no other `eth_getBalance` is made on a path
that shows or uses a balance. Labels, the terminal's and the window's alike: "proved at block N, on
<host>'s word" (yellow, with a warning on Home naming the endpoint; "on one endpoint's word" when
netd named none) or "proved at block N of your node", and yellow "the node's word: <why>". LC6
replaces the head under the same calls.

**As built (LC6, the UI's track, `lc6/ui`).** The same call sites, through the same functions
(`lkd_ui::proved::prove_accounts_at` and the ones built on it), ask `lkd-lc` first: `Status`,
then, while its phase anchors (3, or 6, clock behind), `Account(a)` for every address at once
(`lkd_ui::lc::Lc::accounts_within`, at most `ANCHOR_WITHIN` = 12 s). An anchored answer (anchor
kind 2) is checked again by the UI (`lkd_ui::lc`): its chain, the configured checkpoint in its
identity, `3·signers ≥ 2·committee`, the finalized number not past the block (equal to it for
`AccountFinal`), `header::verify` under the anchor's hash with the anchor's number, and
`mpt::account` under that header's state root giving exactly the account answered. Then the head
cross-check (open decision 18), once per anchored block (`lkd_ui::proved::cross_check`), **as the
decision says since LC7 (D35, lc7-egress)**: the UI asks netd `HeaderAt(N)` (netproto `0x20`),
which netd answers with `Header` (`0x94`), the RLP of `eth_getBlockByNumber(N, false)` as
`reads::header_rlp` re-encodes it, asked of your node or of one public endpoint in turn on
`Head`; `lkd_ui::proved::cross_check_block(netd, N, hash, finalized)` compares its Keccak-256 with
the anchored hash: the same hash is agreement; another is another block at `N`, a verifier
disagreement at or below the finalized number (the value unproved, red "lkd-lc and this wallet
disagree on block N") and "your node disagrees at block N (not final)" above it (yellow); no
answer leaves it unchecked (not green), asked again next time. What the EL route said is kept
for the last 8 blocks, each by its number and hash, finality applied at each call. It names no
address: LC6 asked the account proof at `N` (`ProvedAccounts` at `At { number, state_root }`) of
the address in use, which a review's pin batch or a pool read could tie to a privacy flow by
timing; the verdicts and labels are unchanged. Tokens, pins and pools use the same check before
they show green or gate a flow, and `Included` before it keeps a proved outcome.
Anything `lkd-lc` does not anchor (not running, a phase that anchors nothing, error 7
`NotAnchored`, still fetching, an answer the UI refuses) takes one endpoint's path, labelled
"proved at block N, on <host>'s word, not anchored: <why>" (or "of your node, not anchored:
…"), yellow. Where the configuration names no beacon source (the settings `lkd` passes), or,
for a command typed in another terminal, `lkd-lc` runs no light client, the labels stay LC2's.
Error 7 is a local constant (`lkd_ui::lc::NOT_ANCHORED`) until LC6b's `lc_wire::ERR_NOT_ANCHORED`
is merged; until then `lc_wire` refuses it as reserved, and it reads as "not answering", the
same fallback. Which endpoint proves an address is still today's rule on this path, the provers in
turn from the next one, another after a refusal (open decision 11, one endpoint kept per address,
is `lkd-lc`'s, LC6).

| Where (re-surveyed on `lc2/work`, after the GUI rework) | What |
|---|---|
| `crates/ui/src/tui.rs:5819` `account_reads`, from `refreshed` | The per-address list of the account in use, and the address in use, one `ProvedAccounts` a refresh; `Seen { balance, block }`: `block` is the proved block and `after` the head's, so `history::incoming` and `with_sources` scan from proved blocks; the `block_number` reads stay only where a balance is the node's word |
| `crates/ui/src/tui.rs:5060` `overview`, `:5155` `wallet_lines`, `:4831` `balance_text` | The overview's balance line, each address's line, the Accounts screen: the label, green or yellow |
| `crates/ui/src/tui.rs:5597` `holdings`; `crates/ui/src/tui/scene_of.rs:425` `eth_read_at`, `:491` `total_block`, `:629` `accounts_tab` | Home's dashboard (the window): every address's ETH; through your own node all at once, at the head the last refresh proved (`ProvedAccounts` naming it, no head asked again; a new head only when none is proved there), so Home's balances stand at one block; through public endpoints one address a request in a spread round, each at a head taken for it, the latest (so no endpoint sees them asked together, nor asked at one older block that would tie them); the total says "every balance proved at block N" (green) or "k of n balances the node's word, not proved: <why>" (yellow), each row its own |
| `crates/ui/src/main.rs:1188` `balance` | `lkd balance`: "1.5 ETH (1500… wei), proved at block N, on rpc1.test's word", or the node's word with why |
| `crates/ui/src/main.rs:948` `discover`, `:1036` `used_of` | `lkd discover`: a window of `GAP` addresses at one head at a time; an address used when its proved nonce or balance is above 0; where its proof fails, the pending nonce and the node's balance, said on standard error |
| `crates/ui/src/wallet.rs:1253` `preflight`, `:1495` `preflight_again`, `:1299` `checked_balance` | The pre-flight, and that of a resume, speed-up or cancel: it refuses only when both the proved balance and the node's word fail to cover the plan; a proved balance that does not cover it while the node's word does is a warning in the review (the node decides what it accepts); a balance not proved is a warning too |
| `crates/ui/src/privacy.rs:577` `withdrawn`, `crates/ui/src/pools.rs:686` | After a Tornado or a Privacy Pools withdrawal, the recipient's balance, labelled |

The selected account's `ProvedAccount` (`check_proved`, now `check_head` then `check_account`)
moved to the same query: the overview's refresh, `lkd send`'s and `lkd send --token`'s nonce
(`crates/ui/src/main.rs:913` `proved_account`, from `:1386` and `:1498`). netd's `ProvedAccount`
(`0x11`) stays for `lkd-lc`'s channel (LC1's differential). Before, each `proved_account` ran a
whole `proved_head`, `2n + 1` Tor requests an address (`crates/netd/src/upstream.rs`).

### Stuck, settled and foreign nonces (G11)

Pure functions in `lkd-verified`, beside `reads::pending_nonce`, extracted and proved (25m), over
the proved nonce `p` at the anchor (LC2: at one endpoint's head, a quorum's until 2026-10-28):

- `settled(p, n) ↔ p > n`: nonce `n` is consumed, and no transaction at `n` can be included at or
  after that block (H_nonce); final when it holds at the finalized block.
- `may_replace(p, n, receipt_seen, fresh)`: speed-up and cancel are offered only while `p ≤ n`,
  no receipt has been seen, and the anchor is within `F` (LC2: the head proved at the last
  refresh, so fresh).
- `alarm(last, p)`: `last = some m ∧ p > m + 1`, with `last` from a `GetInfo` asked after `lkd-lc`'s
  answer arrived (LC2: after the refresh's proof), so a send by another client in between cannot
  raise it. Then the values `m + 1` to `p − 1` were consumed by transactions or authorizations
  `keyd` did not sign: every nonce `keyd` releases is at most the ledger's last at any later read
  (7a, 7b), and a refusal gives back only nonces not released (7c). Red only for an anchored nonce
  (open decision 17); on one endpoint's path (LC2 until LC6), yellow: "the node reports nonces lkd
  did not sign".

They add to `unsettled` and `landed`, which keep the node's pending nonce, labelled, because they
ask a mempool question: does the node hold it. A proved nonce past `n` is an extra positive signal
(`landed` may answer `Taken`), never a negative one. On anchored chains they replace
`proved_nonce`'s rule that needs more than one endpoint (`wallet.rs`, `proved_nonce`). `keyd`'s gap
guard (7d) is unchanged, and the review screens of a gap, a resume, a speed-up and a cancel show the
proved nonce ("On chain      nonce 12 proved at block N, on rpc1.test's word; the node's next is
12"). A later `keyd` that signs its own EIP-7702 authorization must record both nonces it consumes
(invariant 5).

| Call site (as built, LC2) | Rule |
|---|---|
| The unsettled line (`crates/ui/src/wallet.rs:1367` `unsettled`, from `tui.rs`'s `App::unsettled`) | Not unsettled once the proved nonce settles `keyd`'s last, whatever the node's pending nonce says |
| A pending transaction's screen (`crates/ui/src/tui.rs:6864` `transaction_lines`, `:4065` `on_transaction`; the window's `transaction_scene`) | Three states ([Never-stuck screens](#never-stuck-screens)): "waiting, not mined at block N (proved nonce p)" with speed-up (u) and cancel (x), or "settled at block N (proved nonce p); inclusion not proved yet" with neither, `u` and `x` doing nothing; `lkd_ui::proved::may_replace`. Without a proved nonce, as before. LC9 (D40): settled, "settled at block F, final (proved nonce p); inclusion not proved yet" once the account at the finalized block F settles it too (`proved::final_account`, asked off the screen's thread by `App::ask_final`, through `proved::at_final` and `proved::nonce_line`); until then the head's line, with "; not final: …" naming your own node's refusal of the proof at F (D42, lc9-wire's words) or a disagreement at F. Speed-up and cancel follow the head's proof alone |
| Resume, speed-up, cancel (`crates/ui/src/tui.rs:6270` `again_prepared`; `crates/ui/src/main.rs:1262` `again`) | A speed-up or a cancel of a nonce the proved nonce settles is refused before `keyd` is asked to prepare it; their review (`:4246` `review_lines`; `lkd`'s) shows the proved nonce |
| The nonce gap's screen (`crates/ui/src/tui.rs:4306` `gap_screen`) | Shows the proved nonce beside the node's next |
| `register` (`crates/ui/src/main.rs:435` `stealth_register`) | Refused when the proved or the pending nonce is above 0, the cautious rule for a privacy warning |
| `discover` (`crates/ui/src/main.rs:1036` `used_of`) | Used when the proved nonce or the proved balance is above 0; the pending nonce as a labelled fallback |
| `lkd history` (`crates/ui/src/main.rs:1062` `show_history`), the History screen and Home's Recent (`App::next_nonce`, `history::Book::status`) | "Dropped" stays the pending nonce's word (the node holds nothing at `n`), labelled "(the node's word)"; a pending transaction with `p > n` and no `Included` record is "settled by nonce at block N (proved nonce p), inclusion unproved", before "dropped". LC9 (D40): "settled by nonce at block F, final (proved nonce p), inclusion unproved" once the account at F settles it (`history::Next::at_final`, `history::Finality`; `lkd history` asks `proved::final_account` for each address with such a transaction), the JSON's `block` F; a record D7 kept still comes first |
| `landed` (`crates/ui/src/wallet.rs:2055`) | `Taken` when the node's next nonce is past it, or else the proved one is |
| "Next on the node", `complete` (`crates/ui/src/wallet.rs:672`) | The pending nonce, labelled, as today |
| The alarm (`crates/ui/src/tui.rs:5882` `alarm_after`; `lkd_ui::proved::alarm_line`; the overview, and Home's alerts, `scene_of.rs:385`) | Yellow on one endpoint's path, from a `GetInfo` asked after the refresh's proof, for the address in use |

### Code-hash pins (G14)

`LkdLc.Pins`, per chain: each contract, its code hash, for a proxy the slot holding its
implementation and the implementation's address and code hash, and the storage conditions (key,
mask, expected value) proved with the pin. The contracts are those the wallet sends to or
reads: the tokens of 23c, the Tornado pools of 21h, the Privacy Pools Entrypoint and pool of
10f, Multicall3, the ERC-5564 announcer and the ERC-6538 registry
(`crates/verified/src/stealth.rs:15-22,362-386`; `egress.rs:88-100`). Measured at mainnet block
26263850 from one untrusted endpoint: USDC is a proxy whose implementation sits at the
ZeppelinOS slot `0x7050c9e0…f8c3`, not EIP-1967's; the Privacy Pools Entrypoint is an EIP-1967
proxy; USDT, DAI and WETH have no EIP-1967 implementation slot. USDT's `balanceOf` and
`transfer` forward to `upgradedAddress` once `deprecated` is set, so its pin holds the packed
(`upgradedAddress`, `deprecated`) slot with `deprecated = 0`. Tornado's Sepolia pools are not
proxies. LC7 surveys each pinned contract for other forwarding (EIP-1967's beacon slot,
diamonds, deprecation flags).

A pin is proved by `eth_getProof(c, keys, {"blockHash": h})` (the implementation slot and the
condition keys) and, for a proxy, `eth_getProof(impl, [], {"blockHash": h})`, the address taken
from the pinned table by typed index and checked equal to the value at the implementation slot;
both on `Shared`. Without that second proof the implementation's code hash would rest on
EIP-6780. Pins are proved at session start, then at most once an epoch and before a review that
touches a pinned contract, never on the automatic overview refresh: about 3.8 KB a contract.

A pin not proved at the current anchor (proof refused, netd withholding, `lkd-lc` down,
syncing, halted or too old, or no answer within `PIN_BATCH_WITHIN`) is "pin unproved", with its
reason. What it does is D1's table, by who holds the funds (`lkd_ui::pins::act`): a deposit
(Tornado, or Privacy Pools through its Entrypoint) and a Privacy Pools withdrawal through
`Entrypoint.relay` are blocked on any cause ("the code of Tornado's 1 ETH pool could not be
checked at block N: <reason>: nothing can be signed"), a blocked Privacy Pools withdrawal naming
ragequit as the exit; a Tornado relayed withdrawal is blocked on a code mismatch of the pool or of
what it uses, and asks an acknowledgment naming the reason (`W`) when unproved or not pinned; a
direct exit (ragequit, a direct withdrawal) and a registration ask `W`, never blocked; a stealth
send is blocked on a Multicall3 mismatch and asks `W` otherwise; a token is red, its balance
unproved, and sending it asks `W`. A failed condition is a mismatch for the flows its `gates` name
and unproved for the others. A new implementation behind a pinned proxy is worded as an upgrade; a
change to the proxy's own code hash keeps the red wording. With no light client configured nothing
blocks: "code not checked: no light client" (the development chain without one keeps today's
behaviour). G14, G16 and any change to when the privacy reviews block get the mixing second review
`AGENTS.md` asks for; as built: [lc7-tokens-ui](#lc7-tokens-ui).

**Restated by LC9 (D51, D58, D60, D39; [lc9-ui-b](#lc9-ui-b)).** The table, what each flow needs
(the target its contract: the Tornado pool, the token), a pin's cause, a pin settled and the
review's act are the gate kernel's, `lkd_verified::pin_gate`, proved in `Spec.PinGate` and refined
(25w); the UI names and words them. A matched pin counts only while fresh (D58): its re-checked
header at most `lc_check::gate_bound_s(chain)` old by the UI's clock (768 s on mainnet and Sepolia,
90 s on the development chain) and `lkd-lc` not in phase 6 (clock behind), counted at each
evaluation of the review: a stale pin is unproved, "proved at block N, 14 min ago: not proved now",
so deposits and Privacy Pools relayed withdrawals block naming its age and the others ask `W`; the
review asks its batch again once the anchor moved past N, keeping that verdict meanwhile (asked
again sooner, `lkd-lc` would answer at once from the reads it holds). "No light client" (D60) comes
only from `lkd`'s settings, from netd's word that it runs no beacon source (`Health.beacon` 0), or
from `lkd-lc` running from no checkpoint where `lkd` passed no settings (`pin_gate::light` of the
configured input and the socket's state): for a command typed in another terminal, a missing or
silent `lkd-lc` is "light client not answering", every need unproved, a deposit blocked. A pin
proved at a block G9's check found replaced is unproved too (D39), its batch asked again as a stale
one is.

**As built (LC7, `lkd-lc` and netd).** `Pin(i)` reads two key sets at the anchor's EL hash: the
pin's slots (`.pin i`: its proxy's implementation slot, then each condition's, `Pins.pinSlots`),
and, for a proxy, the pinned implementation's account (`.pinImpl i`, no key); both on `Shared`,
from the endpoint `el_endpoint(contract, attempt)` picks (your node when the route has one). The
answer's verdict is `Pins.verdict` over the contract's code hash and the slots' values, and over
the implementation's code hash exactly when the proxy's slot holds the pinned implementation:
then the answer carries that code hash and the implementation's account proof; otherwise (no
proxy, or the slot naming another address: upgraded) zero and empty, the implementation field
the address the slot holds (zero without a proxy). An index the chain's table lacks is
`NotPinned` (8), whatever the phase. Every answer carries its certificate (D15) and is checked
again before it is sent; `lkd-lc-plan-test` proves every mainnet pin matched at a recorded block
(`LkdTests.Lc7`), e2e `lc-pins` every development pin, then a code replaced (mismatch), a
condition failed and a proxy moved (upgraded) at an anchor past each change. 25t states it.

### Token balances (G15)

The storage key is `keccak(pad32(owner) ‖ pad32(q))`, `q` the mapping's position from the pin.
Mainnet, measured at block 26263850 against `balanceOf`: USDC 9 (its v2.2 packs a blacklist flag
in bit 255, which the decoding masks: *to confirm*), USDT 2, DAI 2, WETH 3. Sepolia's USDC, WETH
and LINK: *to survey*. The proof is asked on the `Account(owner)` circuit, for all pinned tokens
of the selected address, on an explicit refresh and before a review, at most once an epoch;
other addresses on demand (open decision 4); about 8 KB a token. That `balanceOf` equals the
decoded value while the pin's conditions hold is a reviewed fact per token (H_tok), checked by
an offline differential test against `eth_call` at recorded blocks. This replaces Multicall3's
`aggregate3` of `balanceOf` (`token_balances`, `wallet.rs:879-915`).

**As built (LC7, `lkd-lc` and netd).** `Token(i, owner)` reads one key set at the anchor's EL hash,
`.token i owner`: the owner's balance slot then the token's pin's slots (`Pins.tokenSlots`), on
`Account(owner)`, from the endpoint picked for the owner. The pin byte is computed from those
slots alone, the implementation's code not read (never 4): the session's pin set holds it (D21,
EIP-6780). `MakeTokenSnapshot(owner)` (D22) reads, at the finalized header, the owner's account
(as `MakeSnapshot`) and every pinned token's key set for the owner, all on `Account(owner)`, and
answers `TokenRecord`: the owner's account fact, then one token fact per pinned token whose fact
holds there (25s's held rule); a token whose pin does not match at that block holds no fact and
is left out, so a record never vouches for a red token. `lkd-lc-plan-test` checks every recorded
holder's balance against `balanceOf` (USDC's blacklisted holder frozen), e2e `lc-tokens` the
development chain's against `cast call`, and a token snapshot `CheckSnapshot` holds. 25t states
it.

### Pool roots (G16)

- **Tornado** (Sepolia first, the default): the key of `currentRootIndex`, then `roots[index]`.
- **Privacy Pools**: the pool's `currentRoot`, the Entrypoint's `latestRoot` and `assetConfig`.

The tree rebuilt from the logs, fetched up to block N, must have the root proved at N; the ASP's
leaves are then bound through the proved `latestRoot`. A wrong leaf set with the right root is
a MiMC or Poseidon collision (H_tree, a hypothesis, not computed). This replaces the `eth_call`s
at `pools.rs:165-172`, `:208-230` and `privacy.rs:420-441`. None of these keys is established:
a survey comes first (LC7). Whether a note is spent is never asked of an endpoint, since a proof
would name the note: it is decided locally from the cached withdrawal sets
([The verified cache](#the-verified-cache-g19)).

**As built (LC7, `lkd-lc` and netd).** `Pool(i)` reads, at one anchor (D20), the pool's head
(`.poolHead i`, `Pins.headSlots`), then the root slot its first head value names
(`.poolRoot i x`, `x = headValue …`, `rootSlot`), both on `Shared`; the root's read must read the
same account as the head's. The words are the head's values, then the root's: Tornado's packed
`currentRootIndex` and `nextIndex`, then `roots[currentRootIndex]` (`getLastRoot()`); the PP
pool's depth and size, then the side node at its depth (`currentRoot()`); the Entrypoint's
association-set count and `assetConfig(ETH)`'s four words, then the latest set's root
(`latestRoot()`), or its head words alone while it has no set. `lkd-lc-plan-test` checks every
mainnet pool's root against its contract's at a recorded block, e2e `lc-pools` the development
chain's, and a deposit moving the root. 25t states it.

**Storage keys, derived on both sides.** egress computes each request's keys from typed
arguments and `lkd-verified`'s tables, so neither netd nor the UI picks a key. `lkd-lc`
derives the expected key from `LkdLc.Pins` and looks up exactly that key. The Lean table is the
source; `lkd_verified::pins` is transcribed separately from the spec's text and refined against
it, row by row and derivation by derivation (`LkdProofs.Refinement.Pins`, D16), so the two cannot
differ and still build. A mismatch fails closed.

**In the UI, as built (LC7, lc7-pools-ui, `lkd_ui::pool_proofs`).** A sync asks `Pool(i)` of
every pool it needs at once (the Tornado pools of a shield, a withdrawal, the notes or Home's
totals; Privacy Pools' pool with its Entrypoint), by index in the pin table, never by a
contract the UI names; again while `Pending`, for at most `lc::ANSWER_WITHIN`, once
`proved::shared_wait()` passed, looked at again until it is zero, as a pin batch does (D37). An
answer is believed only after the UI's own check
(D15): the configured chain and checkpoint, an anchor two thirds of the committee signed, the
index asked, and `lc::recheck_storage` at the keys the UI derives itself, `pins::head_slots`
then `pins::root_slot` of `pins::head_value` of the first word, under the pool's pinned
contract; then the head cross-check of the anchored block (`proved::cross_check_block`, D35:
another block there at or below the finalized one is a verifier disagreement, the root
unproved and the overview red). What the words give (D20): a Tornado pool's root at
`currentRootIndex` and its leaf count (`nextIndex`, the second 32 bits of slot 3); Privacy
Pools' state root (the side node at its depth, `currentRoot`) and size; the Entrypoint's latest
association set root and `assetConfig(ETH)`, whose first word must name the pinned pool. The
logs are then read to the anchored block, so the tree rebuilt from them must be exactly the
proved one (and its leaves exactly as many): a Tornado withdrawal's root is the proved root
(`isKnownRoot` is not asked), Privacy Pools' state root, association set root and fees are the
proved ones. Without a light client, or when it proves nothing (down, not anchored, `NotPinned`
as for the development chain's 10 ETH pool, still fetching when the window closes), the flows
read as before, the node's word with the reason in the reviews' root lines, and the public
caches are not used (D23). The reviews say "Root 0x… (the pool knows it: proved at block N)",
"State root 0x… (the pool's, proved at block N)" and "ASP root 0x… (the Entrypoint's, proved at
block N)", or "the node's word; not proved: <why>"; `lkd shielded` and a shield's summary add to
each pool's line "(its deposits proved at block N; its withdrawals are the endpoints' word)", and
the window says the same under its crowds tables (Your notes, a shield's plan: "Deposits proved
at block N; withdrawals are the endpoints' word.") and on the Tornado card ("withdrawals: the
endpoints' word"). Every count of stealth announcements, the crowd a stealth payment hides in
(`lkd stealth scan`, the window's Receive), says "(the endpoints' word)": they rest on the
endpoints' logs and the public cache's mark.

### Inclusion and receipts (G12)

1. After a transaction's receipt arrives, as today, and on `lkd status <hash>`, the UI asks
   `Included(h, block hint, index hint)`, the receipt's block number `N` and index `i` as hints.
   `lkd-lc` answers `Pending` at once and works off the refresh path, at most one G12 a refresh.
2. `lkd-lc` proves `N`'s hash `hN` under an anchored state `A`: by an EIP-2935 storage proof of
   the history contract's key `N mod 8191` (`0x0000F90827F1C53a10cb7A02335B175320002935`,
   `HISTORY_SERVE_WINDOW = 8191`, EIP-2935, Final, at the pinned EIPs commit `e858e91`), valid
   only when `A − 8191 ≤ N < A`; or as the anchor's own hash when `N = A`.
3. It fetches `eth_getBlockByHash(hN, true)` and `eth_getBlockReceipts(hN)`, grouped by `h` as
   netd groups a `Receipt`. netd re-encodes the JSON as typed RLP (untrusted) and pages it.
4. `lkd-lc` checks `keccak(header) = hN` and `header.number = N`, rebuilds both ordered tries to
   the header's `transactionsRoot` and `receiptsRoot`, and checks `keccak(tx_i) = h` and receipt
   `i`'s status. The verdict is final only when the EIP-2935 proof was taken at the finalized EL
   block; a non-final one is proved again once `N` is final.
5. The journal (open decision 19; [`08-accounts-journal.md`](08-accounts-journal.md)): `Mined`
   (kind 2: chain, hash, block, success) is still written on a receipt's word, as today's
   "stop asking" mark, and shown as "mined (the node's word)", never as proved. A new kind,
   `Included` (9, 120 bytes: chain, hash, block, block hash, index, success, final, outcome,
   checkpoint root; [Records](#records)), records the outcome: proved, settled by nonce with
   inclusion unproved, too old, or block too large; D3 says when each is written and how they
   rank after a reorg (open decisions 5 and 19). Kind 6 is `Account`'s, 7 `Snapshot`'s and 8
   `SignedTyped`'s on `feat/approvals-712`, so `Included` is 9.
   `Book::unsettled` skips `Mined`, as today; the list of `Mined` without a terminal `Included`
   drives G12, so a terminal outcome is asked once. This changes `lkd_verified::journal`, which
   `keyd`'s shell decodes for `Remember`: `keyd`'s core and key handling are unchanged, and it
   gets the storage review.

States the UI shows: "seen, not yet proved" while `N` is newer than the anchor; "not provable"
when `N` is more than 8191 blocks back; "inclusion not provable: block N too large to fetch";
"settled by nonce, inclusion unproved", terminal, when the nonce proves `n` consumed and none of
the wallet's transactions at `n` (original, speed-ups, cancel) could be proved. A refusal backs
off before the next try.

**G12's states, as built (LC8, `lc8/ui`, `lkd_ui::included`).** Beside the receipt, which
stays the node's word, in the history (`lkd history`, the History screen, the window's
Activity), the transaction's screen, the overview's list and `lkd status`:

| State | Words | Colour | Kept (D3, D7) |
|---|---|---|---|
| Not asked or nothing answered | "mined in block N (the node's word)" | yellow | |
| `Pending` after 15 s, or ahead | "…; seen, not yet proved" | yellow | |
| Proved, final | "mined in block N at index i, succeeded (proved)" ("failed", red) | green | outcome 0, after the head cross-check |
| Proved, not final | "… (proved, not final)" | green | no: asked again |
| Kept under a checkpoint since moved | "… (proved under an earlier checkpoint)" | green | the record stands |
| Too old, plausible | "…; not provable: more than 8191 blocks back" | yellow | outcome 2 |
| Too old, sent too recently for it | "…; the node mislocated it: block N is too old for when it was sent" | yellow | no: asked again |
| Too large | "…; inclusion not provable: block N too large to fetch" | yellow | outcome 3, own node or two public endpoints; else next session |
| D4 answered no, public route | "…; inclusion not checked on public endpoints (your choice)" | yellow | |
| Refused | "…; the light client refused the node's receipt: <check>" | red | no: backoff, 1 min doubling to 1 h |
| The UI's check refused the answer | "…; verifier disagreement: <reason>" | red | no: backoff |
| No receipt, nonce consumed at a finalized block | "settled by nonce at finalized block N, inclusion unproved" | yellow | outcome 1 |

A transaction the wallet did not send, at its nonce, cannot be located
or named without secp256k1 public-key recovery, which `LkdLc` does not have: not in v1 (open
decision 22); the
state stays "settled by nonce, inclusion unproved", and the G11 alarm covers nonces `keyd` never
signed.

**Sizes** (LC8, measured 2026-10-26 with `vectors/inclusion/fetch.py`, the JSON as the endpoint
sent it, the RLP as netd will re-encode it):

| Block | Transactions | Block JSON (`true`) | Receipts JSON | Transactions RLP | Receipts RLP |
|---|---|---|---|---|---|
| mainnet 26,270,755 (the largest, 747,345 bytes, of 709 at least 90% full among 8,000) | 327 | 1,651,475 | 1,352,911 | 746,211 | 378,212 |
| mainnet 26,270,767 (the most transactions of those measured) | 497 | 1,659,262 | 1,636,469 | 709,713 | 441,603 |
| mainnet 26,274,730 | 230 | 1,474,373 | 4,004,659 | 680,442 | 1,010,164 |
| Sepolia 11,985,890 (the largest, 969,024 bytes, of a week's 5,599 at least 40% full) | 274 | 2,065,376 | 654,941 | 967,914 | 175,915 |

The EIP-2935 proof (`eth_getProof` of the history contract's slot) is 11.3 to 11.4 KB of JSON,
6.3 KB of nodes. Mainnet's 60M gas limit has made the block and its receipts two to five times
the earlier measure (408 to 463 KB, 828 to 859 KB); a logs-heavy block's receipts reach 4 MB of
JSON, still under netd's `MAX_BLOCK_BODY` (8 MiB, `http.rs:23`), which both requests take, a
block beyond it being the "too large" outcome. Sepolia's 200M gas limit allows larger, so far
calldata-heavy rather than larger in receipts. Egress relaxes `third_party_ok`
(`crates/verified/src/egress.rs:496-528`) for these two requests only (open decision 23): by
hash, in the transaction's group, after a receipt located the block. That circuit already knows
the hash; it learns the block.

**Cost** (To confirm 10): the verdict on one transaction, rebuilding both tries, takes 0.13 to
0.23 s on average and 0.50 s at worst on those four blocks (every transaction of each, 1,328 in
all, on the benchmark's machine, a shared host); a root takes 75 to 200 ms, nearly all of it
Keccak-256 (`LkdBase.Keccak` hashes 1 MiB in about 110 ms). The process stays below 21 MB
resident, the inputs 1.1 to 1.7 MB of it. LC8's acceptance, 1 s per transaction, holds on both
chains.

#### Inclusion, as built (LC8, core)

Built on `lc8/core` (off `feat/light-client` 68cbd5c), Lean only; phase 2 wires it (below).

* **The ordered trie root** (`LkdLc.El.Trie`): the Yellow Paper's structural composition
  function c(𝔍, i) and node cap n(𝔍, i) (Appendix D), built as RLP in `ByteArray`s over the
  items' spans in netd's buffer, its recursion as deep as a key's nibbles (an index's RLP has at
  most 18), the keys' common prefix a left fold. Its specification is `Spec.Mpt.Trie`
  (`LkdProofs/Spec/MptTrie.lean`), the Yellow Paper trie model of `proof/mpt-trie` (3c2ee7c),
  copied here unchanged but for one import (`LkdProofs.Spec.Common`, which this line's
  `Spec.Mpt` shim does not bring) until that branch lands: then its file is kept, with that
  import. `Lc.Trie.node_eq`: `node`'s RLP is `compose`'s of the same pairs; `orderedRoot_eq`: a
  root built is TRIE of the ordered map (item `i` under `rlp(i)`); `orderedRoot_lookupB`,
  `orderedRoot_soundB`: under it the model's proof of `rlp(i)` reads item `i` with
  `Spec.Mpt.lookup`, and any proof reading otherwise holds a Keccak-256 collision
  (`Spec.Mpt.Trie.lookup_complete`, `binding`).
* **Envelopes** (`LkdLc.El.Typed`): EIP-2718 transactions of types 0 to 4, each field of its
  type's shape (the execution specification's `LegacyTransaction` to `SetCodeTransaction` at
  execution-specs `e1a316a0`), nested lists read two levels deep; receipts
  `[status, cumulative_gas_used, bloom, logs]` of the same types, the status EIP-658's (`0x01`
  or empty; a state root refused). Amsterdam, at the pinned EIPs commit (EIP-7773's scheduled
  list), adds no transaction type and no receipt field. `Typed.txType_spec`, `receipt_spec`,
  `items_spec`.
* **EIP-2935** (`LkdLc.El.History`): `blockHash` reads slot `N mod 8191` of the history
  contract, whose account must hold the EIP's runtime code, a nonzero value padded back to 32
  bytes. `History.blockHash_spec`, `blockHash_binding`. Amsterdam keeps the contract and its
  layout (EIP-7928 records its write in the block access list, EIP-8037 changes the system
  call's gas).
* **The verdict** (`LkdLc.Inclusion.verdict`), a pure function of the anchor (hash, state root,
  number, finality), the receipt's block number and index hint, `N`'s hash proof (the anchor
  itself, or the history contract's account and storage proofs), `N`'s header RLP and its two
  lists (`none` when netd found them too large): `proved` (index, status, final), `ahead` (`N`
  newer than the anchor), `tooOld` (more than 8191 older), `tooLarge`, or `refused` with the
  first check failed (`hashProof`, `header`, `body`, `notInBlock`, `transaction`, `receipt`,
  `transactionsRoot`, `receiptsRoot`). A wrong index hint is searched for by hash; each list
  is refused from 4 GiB. 25l: `Inclusion.verdict_proved`, with `verdict_ahead_iff`,
  `verdict_tooOld_iff`, `verdict_tooLarge`. Phase 2 put the checks in D36's order (below).
* **Tests**: `lake exe lkd-lc-incl-test` (`proofs/tests`) proves every transaction of the kept
  mainnet and Sepolia blocks, times each, and checks every other outcome and a changed byte of
  each input.

**anvil** (To confirm 4): Foundry 1.5.1's anvil, `scripts/foundry.sh`'s, panics on
`--hardfork amsterdam` ("unimplemented Amsterdam", `crates/anvil/src/hardfork.rs:61`); its
default, Osaka and Prague give 21-field headers. It deploys no history contract and runs no
EIP-2935 system call, even with the contract's code set by `anvil_setCode`: the slots stay zero
as blocks are mined. So the e2e chain sets the code with `anvil_setCode` and, before each block
`A`, block `A − 1`'s hash at slot `(A − 1) mod 8191`; the parent-hash mode (Amsterdam headers)
stays the fake beacon's synthetic headers of LC6. Anvil proves a block from the state it holds
for it, which `anvil_setStorageAt` changes for good while the block is the newest (checked on
1.5.1: every proof at a block planted after holds under no state root). With automine off, the
chain therefore writes the slot by a transaction of EIP-2935's system address to the contract
inside block `A` itself, as Prague's system call does (the contract's own `set`), and no mined
block's state changes: G12's final answer, proved at the finalized block, depends on it.

#### Inclusion, as built (LC8, phase 2)

Built on `lc8/phase2` (off BASE_B 0c4a852, with lc7-core's SCAFFOLD_FIX 944b844); lc8-ui shows
it, journal kind 9 its record:

* **D36's order** (`LkdLc.Inclusion`): `settle (q, hN, header, body)` checks `N`'s header against
  `hN`, the lists' shape, the transactions root, the receipts root, then looks the hash up
  (`notInBlock`), then the envelopes; `verdict` is the window, `hashOf`, then `settle` at the
  hash it proves with the anchor's finality. A `notInBlock`, `transaction` or `receipt` refusal
  says what the proved block holds (`verdict_notInBlock`, `verdict_transaction`,
  `verdict_receipt`: a header bound to `hN`, both lists rebuilding its roots, and for the
  envelope refusals transaction `j` hashing to `h`, refused by `Typed.txType`, or accepted while
  receipt `j` is no receipt of its type), and a result settled once is the verdict under any
  anchor proving the same hash (`verdict_eq_settle`). 25l restated.
* **G12's job** (`LkdLc.PlanIncl`, D13, D14): one job, fetching one request at a time once its
  proving header is bound: EIP-2935's slot at that header (`ElStorage(…, HistoryFor(N, h))`,
  none when `N` is its own block), then `ElBlock(…, h, hN)` to its last page, then
  `ElReceipts`. When the receipts come, or the block came too large (flag 1, or the receipts
  `TooLarge`), `settle` runs once and its result is kept with `N`'s header and its Prop witness,
  the buffers dropped, at most 8, one per transaction and `hN`. A refusal before both roots
  matched, and too large, are asked again with `attempt + 1` (another endpoint) and kept only
  after `maxAttempts`; the receipts alone are asked again when they were the cause. A failed
  fetch ends the job `Unreachable` after as many, a proving header given up `Refused` or
  `Unreachable` (SCAFFOLD_FIX's `ElHeader(0, h)`), told for `errorMs`, then resumed.
* **The handler** (`LkdLc.Included.includedLight`): `NotAnchored`; `ahead` and `tooOld` from the
  anchor's EL number, no fetch; `Busy` while the job fetches bodies for another transaction;
  else the job pointed at the transaction and the proving header named now (the finalized one
  when `N ≤ F ≤ N + 8191`, final; else the anchor), and the answer only from that header's RLP
  bound again (25j), a history proof at it whose `hashOf` is some `hN`, and a result settled at
  `hN`, with its certificate (D15); when the anchor moved, only the history proof is fetched
  again. 25u (`included_sound`) has `anchored_sound`'s shape with no run invariant.
* **netd** (`lc_bodies.rs`, D11): `eth_getBlockByHash(hN, true)` and `eth_getBlockReceipts(hN)`
  from `g12_endpoint(tx, attempt)` (your node when the route has one; else the endpoints that
  took the broadcast first, else D4's fallback), re-encoded by `envelopes`, `N`'s header by
  `header_rlp` (it must hash to `hN`); past `MAX_BLOCK_BODY` the header alone from the same
  endpoint, flag 1; receipts past it `TooLarge`; `null` `NotFound`.
* **Measured** (`lkd-lc-incl-test`, the whole job through `Lc.step`, from the `Included` query to
  the proved answer, pages of 61,421 bytes, the benchmark's machine): mainnet 26,270,755 (746 KB
  and 378 KB of RLP in 13 and 7 pages, with the history proof) 0.27 s; Sepolia 11,985,890
  (968 KB and 176 KB in 16 and 3 pages, the block proving itself) 0.27 s: within LC8's 1 s.
* **Tests**: `lkd-lc-incl-test`'s job cases (ahead, too old, too large with `N`'s header bound
  after three attempts, receipts refused then asked again alone, `notInBlock` settled at once
  after both roots, proved not final then final with one history fetch and no body, `Busy`, a
  wrong hint), each proved answer checked as 25u states it; netd's against fake nodes serving
  the kept blocks' JSON; e2e `lc-mined`.

### The node's proof window

`eth_getProof` at the anchor needs the node to hold that state:

- **geth**, path scheme (the default for new databases): proofs over 128 diff layers; older
  ones need `--history.trienode`, off by default; `--history.state` (90,000 blocks by default)
  serves historical values, not tries. The hash scheme keeps 128 tries in memory. The anchor
  (one or two slots behind the head before Gloas, at least two under it) and the finalized
  block (two to three epochs, 64 to 96 slots, behind) are within 128.
- **reth**: `--rpc.eth-proof-window` defaults to 0, proofs at the tip only (maximum
  1,209,600). With the default, every anchored proof is refused.

A refused proof leaves the value on the yellow path, with the reason (LC9, D42; as built,
lc9-wire). netd reads the JSON-RPC error of the light client's `eth_getProof` by block hash
(`ElProof`, `ElStorage`; `rpc::node_error`): code 4444 (execution-apis' "pruned history
unavailable"), or a message containing "proof window" (reth's `-32602` "distance to target block
exceeds maximum proof window"), "missing trie node" (geth's `-32000`) or "historical state", in
any case, matched on the raw text, is `Failure::Pruned`, its message kept sanitized as every
node error's (`rpc::sanitize`); a 4444 on a block or receipts read stays `Node`. From your own
node it is the channel's `Window` (12), on which `lkd-lc` ends the read with `NodeWindow` (9);
from a public endpoint it is `Node` (4), and the next endpoint is asked. The UI names the refused
read's block from `Head` (`lkd_ui::lc`): F, the finalized block, for `AccountFinal`,
`MakeSnapshot`, `MakeTokenSnapshot`, a final `BlockHash` and an `Included` F proves, the anchor
otherwise, each asked at most once a slot: "your node refuses proofs at block N (reth:
--rpc.eth-proof-window; geth keeps the last 128 blocks' state)", or "at the light client's
block" when `Head` names none. Settings' "Execution proofs" says it beside the head cross-check
until a read of that kind is answered again; no per-endpoint record is kept. The rule only names
a reason, never changes a value: a refused read is unproved either way, and D1 counts it so.
`lkd doctor` stays offline, contacting nothing (`crates/launch/src/doctor.rs:1-3`): from the
configuration alone it says to set `--rpc.eth-proof-window` to at least 256 for a reth node,
that final proofs read the finalized block, 64 to 96 blocks back and more while the chain does
not finalize, and where a refused proof is said (`lkd balance`, `lkd status <transaction>`).
End to end: the e2e `lc-proof-window` (As built, lc9-wire).

## The verified cache (G19)

The user's addition of 2026-10-26: the light client keeps the state the wallet uses, its pool
trees, notes' spent status, stealth announcements and the user's own balances, nonces, token
balances and ENS names, as a cache built while the wallet is used. Today nothing is kept:
every pool sync rebuilds the Tornado and Privacy Pools trees from deployment
(`crates/ui/src/pools.rs:138-205`, `wallet.rs:745-797`) and a stealth scan starts from the
announcer's deployment (`wallet.rs:704-710`). Its rules:

- **What normal use already proved, nothing else.** Nothing is prefetched: the cache adds no
  request and so no fingerprint. Later syncs ask only for what is new.
- **Evidence, not state**, as for [the evidence file](#the-evidence-file): whatever is
  persisted is checked again when it is loaded, and a file that fails is set aside and
  rebuilt, never believed.
- **Never shown as current.** A cached value is shown as "proved at block N, 3 h ago", beside
  the fresh proof the wallet asks for as before; the request budget is unchanged or lower.
- **Final only.** Only facts at finalized blocks persist; a fact at a head that is not final
  stays in memory and is withdrawn by a reorg (G9).

**Public caches**, the same for every user who synced the same range: they name no address,
but they show anyone who reads the disk which pools this wallet synced, and up to which block
(D34, said in Settings' Public caches row): in one plain file per chain in `lkd-lc`'s directory, `<home>/lc/<chain id>.cache`, a region per
cache with two slots of its own, written in place as the evidence is ([The evidence
file](#the-evidence-file)), opened before the sandbox, so 26a gains one descriptor and no path
access (26a restated, with its second reviewer; the file as built below).

| Cache | Content | Checked by |
|---|---|---|
| Pool trees | Per pinned Tornado and Privacy Pools pool: its leaves in order, the tree's frontier, the block `N` and the root proved at `N` (G16); the ASP's leaves with the `latestRoot` they rebuild | Leaves fetched after `N`, appended to the frontier, must give the root proved at the new anchor (G16, H_tree); a mismatch discards the cache and syncs from deployment. Loaded, the stored leaves must rebuild the stored root, which is used only as a starting point |
| Withdrawal sets | Per pool, the nullifier hashes of its `Withdrawal`, `Withdrawn` and `Ragequit` logs, and the last block scanned | Per log, the endpoint's word, as today; completeness is not proved (N1). In return a note's spent status is decided locally, never by a request that names the note, which egress refuses ([Pool roots](#pool-roots-g16)) |
| Stealth announcements | The announcer's `Announcement` logs and the last block scanned | As today: per log the endpoint's word, completeness not proved (N1). Detection with the viewing key stays where it runs today |

**The file, as built (LC7, `lkd_lc::cache` over `lkd_verified::cache`, 25v).** `lkd-lc` opens
it when it serves, never in `--propose` or `--check`: `O_RDWR | O_CREAT | O_NOFOLLOW |
O_CLOEXEC`, `0600`, an exclusive `flock`; a lock another `lkd-lc` holds, a chain without caches
or any error leaves it without caches, said on standard error, and the shell then answers the
cache frames `Unsupported`.

| Offset | Size | Content |
|---|---|---|
| 0 | 4 KiB | Header: `LKDLCCA1`, version (4, `1`), chain id (8), region count (2), then per region its id (2), item size (4) and capacity (4); zero to 4 KiB |
| per region, in `cache::regions`' order | 4 KiB | Two slots of 128 bytes: `LKDC`, sequence (8), count (4), block (8), root (32, zero for a set), digest (32, Keccak-256 of the first `count` items), then zeros; zero after the slots |
| after its slots | capacity × item size, to whole pages | The region's items, append-only |

A header other than this release's for the chain (a new file, another version, chain or region
table) resets the file: truncated, the header written, every region empty. Each region is
loaded from the slot `cache::choose` picks among those that decode, fit the region (count
within its capacity, a root only for a tree) and carry their items' digest; none, and the region
is empty. An append is whole items, at the staged end (the committed count when nothing is
staged) or at 0, which empties both slots and syncs them before anything else; a commit names
the staged end as its count, a block not below the committed one and no root for a set, and
syncs the items, then writes the slot not in force with the next sequence, then syncs it. One
connection stages a region at a time; another live connection's append or commit is `Busy`,
and a closed connection's staging is dropped (the shell's `discard`, lc8-channel), the items it
wrote left past the committed count until appends overwrite them. The file is sparse: only what
was appended is written. The ids, item sizes and capacities are the allocations' cache table's,
with the capacities in [As built, lc7-cache](#lc7-cache).

A delta's starting block tells an endpoint when the wallet last synced; it is rounded down to a
grid (open decision 26), so that many wallets share each starting block.

**In the UI, as built (LC7, lc7-pools-ui, `lkd_ui::cache`).** A region is loaded once a
process, at its first use: its committed items read page by page (`CacheRead`), then checked
against the newest `CacheMark` (journal kind 10) this wallet wrote, read from `keyd`'s history
on the connection the flow already holds (`keyd` serves one at a time): the first `count`
items must have its digest; items past them are dropped (a commit whose mark was not written)
and the region is rewritten from item 0 at its next commit; no mark, or another digest,
discards the region, which is synced from deployment. A tree's and the association set's items,
all marked, must rebuild the root stored with them. Without the marks (`keyd` locked) or a
cache (`lkd-lc` without its file, or answering `Unsupported`), nothing is read or written, and
the syncs are today's. A delta starts at the block a region is complete through, rounded down
to the grid (D6: 50,000 blocks, 32 on the development chain), never before deployment; what it
fetches again is dropped, a tree's leaves by index (each must be the cached one) and a set's
items by block (those at or below the cached end must be the cached ones, in any order; if not,
both are used and the disagreement is said). A tree is fetched to the block the light client
proved its root at and must give that root and leaf count (`cache::tree_extends`); if not, the
delta is fetched again (netd's rotation asks the next endpoint), and when the cache contradicts
what was fetched (another leaf where it holds one, more leaves than proved, another root over as
many) the region is discarded and synced from deployment. Fewer leaves than proved is the
endpoints behind the anchor, which no resync mends: that sync fails, saying so. Privacy Pools'
deposits and withdrawals are checked with its tree: each deposit's commitment recomputed from
its value, label and precommitment, and with the withdrawals' new commitments, the tree's
leaves, as many. A set without a root (Tornado's spent sets, Privacy Pools' ragequits, the
announcements) keeps a closed grid cell only once two fetches of it returned the same items,
an earlier sync's this session or, failing one, the cell fetched again at once; a mismatch keeps
neither and is said (`lkd: …` after a command, Settings' row in the window and the terminal);
every item fetched is used now, kept or not. Only what is final is kept: items at or below the
finalized EL number of the anchored answer (a set's closed cells; a tree's leaves, with the root
rebuilt over them; for announcements, the finalized block of the last anchored account the UI
checked; the association set, whose labels carry no block, with the finalized number of the
answer that proved its root, used only while a newly proved root is the one it rebuilds).
Commits: at most every 10 minutes a region (after each of the UI's jobs, on a thread of its own,
one transfer at a time, never on the refresh's path) and at exit (within 3 s, beside the
snapshot; a command commits as it ends), each one `CacheSession`: the appends at the region's
end, or at 0 to rewrite it, whole items in frames of at most 65,529 bytes, then the commit, back
to back, then `Remember` of the `CacheMark`, asked again while another job holds `keyd`. A
commit `lkd-lc` refuses (another of this wallet's processes committed meanwhile) drops what
this process holds of the region and the chain's marks, which are read again. Settings' rescan
first empties every region of the chain in `lkd-lc`'s file (a `CacheSession` per region: one
zero item appended at 0, which empties both of its slots, then the session dropped, nothing
committed), then writes a mark of nothing for each: each is synced from deployment at its next
use and rewritten from item 0. Emptying the file first is the second review's fix (2026-10-28):
another of this wallet's processes that read the marks earlier still held a region at its old
end, and appended and committed there, its newer mark undoing the rescan; its append is now
refused, and it reads the marks again. A region `lkd-lc` does not empty (not running, or a
transfer of another process under way: `Busy`) fails the rescan, with no mark written. A cached Tornado leaf keeps no deposit time: a note whose
leaf was read from the cache is "deposited more than <age> ago", the first deposit fetched after
it bounding its age, on which its cover tier rests, or "at an unknown time"; the withdrawal
guard warns that the time is not known unless that bound is at least a day old.

**Your facts, as snapshots**, in `keyd`'s encrypted journal (the user's choice, open decision
25): a record kind of its own, `Snapshot` (7), encrypted with the journal's keys as history,
contacts and notes are, readable only after unlock. A snapshot holds, for one finalized block:
the signed update that finalized it, the EL header's RLP, and the facts shown (each account's
nonce and balance, each token balance; ENS names in LC9, D5), each with its proof. The UI writes one
after a refresh whose answers were proved and final, at most every 10 minutes and at exit, in
records of at most one lcproto frame each (as built, below), as it writes history records today; `keyd` stores it and checks nothing in it,
as for every journal record. At start, after unlock, the UI shows the newest snapshot's values
with their block and age, and hands the record to `lkd-lc` (lcproto `CheckSnapshot`, a new
query): `lkd-lc` verifies the update's signature with that period's committee from the
evidence, the EL header against it (25j) and each proof (25k), and answers which facts hold. A
fact that does not is dropped as soon as `lkd-lc` says so (until then it is shown as your last
session's, being checked, never as current); a snapshot older than the evidence's reach
(`MAX_AGE` from the configured checkpoint) is shown as not proved, in grey, and dropped at the
next snapshot.
This restates the journal codec row (the storage review).

**Your facts, as built (LC6, `lc6/snapshots`).** Accounts (nonce, balance, storage root and
code hash) are the facts written; token balances since LC7 (fact type 2, from
`MakeTokenSnapshot`, D22: [Token balances](#token-balances-g15)); ENS names since LC9 (fact type
3, D47, D48): the selected account's primary name, made by the UI in each pass but the one at
exit ([`17-ens.md`](17-ens.md#names-as-snapshot-facts-lc9)), in place of the follow-up
`lc9/ens-facts` (D5).

- **The record** is [`Frame layouts`' snapshot record](#snapshot-records): one finalized EL block,
  the update that finalized it, the header, the facts, at most one `CheckSnapshot` frame; a larger
  set is split into self-contained records (the split rule there), not 256 KiB as first planned.
- **Writing** (`lkd_ui::snapshot::make`, from the refresh, `App::snapshot_due`): after a refresh
  whose balances `lkd-lc` anchored, the first of the session at once, then at most every 10
  minutes, on a thread of its own, the UI asks `MakeSnapshot` for each of those addresses (again
  while `Pending`, 20 s in all), checks each record again as it checks an anchored answer
  (`header::verify` under the header's own Keccak, at the record's block and time;
  `mpt::account` under its state root giving exactly the fact: `snapshot::recheck`), merges those
  of one block and splits them (`snapshot::split`), and has `keyd` keep each with `Remember`. At
  exit, when a refresh anchored balances since the last write and none was written in the last
  minute, the same, waiting at most 3 s; a change of chain writes none. Only facts at the
  finalized EL block are written: `lkd-lc` reads them there. **Requests, a departure from "the
  cache adds no request"**: as built, the anchored `Account` reads are at the anchor, never final,
  so a snapshot reads the finalized block's header and each address's proof again, by hash, on
  the address's own endpoint (one `ElHeader` and one `ElProof` per address, at most every 10
  minutes and at exit; the refresh asks one `ElProof` per address every 20 to 40 s).
- **Keeping** (`crates/keyd/src/journal.rs`): `keyd` checks nothing beyond the codec
  (`journal::decode_record` of kind 7 is `snapshot::decode`). Per chain it keeps the snapshot
  records of the two newest blocks written, at most 8 records a block, for the four chains written
  last (`journal::superseded`); the rest leave `History`'s list at once, and the file when `keyd`
  next opens it: it writes the records it keeps under a new epoch, with a fresh salt, from counter
  0, into `journal.new`, syncs it, renames it over the journal and syncs the directory (a crash
  before the rename leaves the old file whole). A session writes at most 8 MiB of snapshots, none
  once the file passes half its 64 MiB cap; past that, a snapshot is kept for the session only.
- **Reading** (`App::load_snapshot`): at start, on a thread of its own, once `keyd` answers
  (after unlock, asked every 500 ms for at most 10 minutes), its chain and its history; the
  records of the block of the last snapshot written for that chain (`snapshot::newest`, an
  address's last written fact standing) are shown at once: each value, before the first refresh,
  "Cached  0x… 1.5 ETH, nonce 3 (proved at block N, 3 min ago; from your last session, checking)"
  in a style of its own (cyan in the terminal, information in the window; grey once too old),
  never in a current value's green or yellow; then each record goes to `CheckSnapshot` (again
  while `Pending`: `lkd-lc` loads its evidence, or its store has not reached the sync period the
  snapshot's update was signed in, as after a refreshed start; 60 s in all). A fact not held, or a
  record refused, is dropped; a fact too old stays grey, "older than the light client's evidence,
  not used", and out of Home's total; one not checked (no light client, `lkd-lc` not answering,
  still `Pending` after 60 s: "the light client has not reached it yet") stays labelled so. Until the refresh gives a value, the overview's balance, the account's address lines and
  Home's total and All accounts show the snapshot's, labelled; the refresh's replaces it as
  before. A line under the balance (and a text under Home's total) says the light client's word
  on the snapshot ("Snapshot of block N from 3 min ago: 2 facts confirmed by the light client",
  "… 1 fact not held, dropped") and the last one written ("Snapshot saved: block N, 2 facts").
- **Checked** in `lkd-lc` (`Lc.checkSnapshot`, [Frame layouts](#frame-layouts)): the update
  under the committee the store holds for its period (`Store.verifyHistorical`), the header
  bound to its finalized header (25j), each proof (25k); the theorem is 25s's snapshot clause
  (`Lc.snapshot_held`). An update of a period the store has not reached yet is `Pending`
  (`Lc.ahead`, `Lc.checkRecord_pending`), not refused: until 2026-10-26 it was refused, and a
  restart after a refresh dropped a genuine snapshot as forged (e2e `lc-snapshot`).

**What it changes for an attacker.** A tampered public cache costs a resync, a tampered
snapshot a missing value. A withheld withdrawal log makes a spent note look unspent: its
withdrawal is then refused on chain, costing gas, and the overview says the spent status rests
on the endpoints' logs. With the public caches (LC7), a withheld log is kept only if both
fetches of its closed cell withhold it, each from the next endpoint when two or more are
configured (D8's two-fetch rule); otherwise the cell is not kept and the next sync fetches it
again, so one lying endpoint does not make an omission permanent. A compromised UI, which
writes both the items and the mark, can append set items (a spent nullifier, an announcement, a
ragequit) that stand until Settings' rescan; it cannot make a tree or the association set pass,
which every use checks against the root the light client proved. The caches name no address,
but show at rest which pools were synced and to which block (D34).

## Sources and egress

### The beacon API

| Request | Answer | Size |
|---|---|---|
| `GET /eth/v1/beacon/light_client/bootstrap/{block_root}` | `LightClientBootstrap` | 25,672 B |
| `GET /eth/v1/beacon/light_client/updates?start_period={p}&count={c}` | up to `c` updates, the best per period | 26,424 to 26,933 B each, plus 12 of framing; about 58 KB in JSON |
| `GET /eth/v1/beacon/light_client/finality_update` | `LightClientFinalityUpdate` | 2,090 B |
| `GET /eth/v1/beacon/light_client/optimistic_update` | `LightClientOptimisticUpdate` | |
| `GET /eth/v1/beacon/blocks/{slot}/root` | JSON only; 404 for an empty slot | for `--propose` only |

**SSZ.** With `Accept: application/octet-stream` the four light-client endpoints answer SSZ
(beacon-APIs `79b9b05`). Bootstrap, finality and optimistic updates carry `Eth-Consensus-Version`
(`phase0` to `gloas`; `fulu` names the Electra types). `/updates` has no such header (Lodestar
adds a comma-separated one, not relied on): each chunk is a little-endian `uint64` length, a
4-byte fork digest, then the SSZ, and **the length counts the digest** (length = 4 + SSZ length;
the specification text, Lighthouse, Nimbus, Lodestar, Teku and Prysm, and a live Lodestar
answer: 26917 = 4 + 26913). The digest is `compute_fork_digest(gvr, epoch(attested slot))`,
BPO-aware; the beacon-API text still shows the old signature, but every serving client computes
the BPO-aware one. Every check runs on the SSZ bytes, since `hash_tree_root` is defined over
them. A source that answers only JSON (a public Lighthouse endpoint did, to an SSZ `Accept`) is
re-encoded to SSZ by netd, untrusted (open decision 1): a re-encoded `/updates` chunk carries the
item's `version` name as a one-byte fork tag instead of a digest (`u64le(1 + s)`, fork, SSZ:
`0` Electra, `1` Fulu, `2` Gloas, the evidence's numbering), which `lkd-lc` checks against
`Forks` at the attested slot, so netd keeps no fork schedule and computes no digest; the digest
check (25a) applies to SSZ-native chunks only. A bootstrap, finality or optimistic update
reaches `lkd-lc` with the name its source gave, native or re-encoded ([Frame
layouts](#frame-layouts)).

**As built (LC6a, `crates/netd/src/beacon.rs`, `reencode.rs`).** netd tells SSZ from JSON by the
answer's `Content-Type`: `application/octet-stream` is forwarded as received (a bootstrap's, a
finality or an optimistic update's with its `Eth-Consensus-Version` value, which must be 1 to 16
lower-case letters and digits, else `Node`; an `/updates` answer as form `0`, its chunks unread);
`application/json` is re-encoded; anything else is `Node`. netd has SSZ types for the versions
whose light-client containers are Electra's, `electra` and `fulu` (Deneb's execution payload
header, an execution branch of 4, committee branches of 6, a finality branch of 7), so it
re-encodes those, a bootstrap, a finality or an optimistic update keeping its JSON `version`
(else the header's), `/updates` as form `1`, one chunk per item with the fork byte `0` or `1`;
any other version, `gloas` included, which no JSON-only source serves (Lighthouse has no Gloas
light client), is `NotSsz`. The re-encoding is checked byte for byte against recorded mainnet
answers (`crates/netd/tests/fixtures/beacon`: a public Lighthouse endpoint's JSON bootstrap and
`/updates` for two periods, against a Lodestar node's SSZ of the same objects). A block's root is
read from the JSON's `data.root` (`Accept: application/json`, since the beacon API serves it in
JSON only). `404` is `NotFound`, `403` and `429` (the source refuses Tor) `Unreachable`, any
other status but `200` `Node`.

**Which clients serve it.** Lighthouse (on by default since v7.0.0), Nimbus and Lodestar serve
it by default; Teku and Prysm behind flags; Grandine not at all. None backfills: bootstraps
exist only for finalized checkpoint roots seen while synced. Lighthouse v8.3.2 has no Gloas
light client (`GloasNotImplemented`), so on Sepolia it is not a source; Lodestar serves Gloas
data (seen live), and Nimbus, Prysm and Teku have code for it (on the wire, *to confirm*).
Lodestar's public nodes served history back to mainnet period 1605, Sepolia 1063 and Hoodi 196.

### Sources, configured

- **Your beacon node**, when you run one: as an onion service (`beacon = onion`, the node's
  service key with another port), or on loopback TCP (`beacon = 127.0.0.1:5052`) on the TCP
  route only. On the IPC route netd's network namespace is empty, so it cannot be reached;
  Settings says so.
- **Public beacon endpoints**, keyless, through tor, as 06's public endpoints are: over TLS 1.3
  (`beacon_public = host[/path],…`), or in plain HTTP to port 80 for a source that serves no
  TLS (`http://host[/path]`, the Nimbus team's mainnet node). Plain HTTP is for beacon sources
  alone, which every object's checks make safe to reach so ([Egress
  v8](#egress-v8-invariant-10i)); `public`, `relayers`, `asp` and `pp_relayers` refuse
  `http://`, and a source counts once whatever its scheme. Settings ("…, plain HTTP over Tor",
  "…, over Tor and TLS"), `lkd doctor` and `lkd settings` ("(plain HTTP over Tor)", "(TLS over
  Tor)") say how each source is reached, and `lkd settings` says so again when a plain one is
  added. Through Tor by default; `beacon_route = direct` (open decision 28) reaches them over
  this machine's own network instead ([The direct route](#the-direct-route-decision-28)), as Tor
  turned off does (`route = direct`, `lkd --no-tor`: no tor runs), and every place that says
  "over Tor" then says "directly". `lkd init` suggests those the survey
  finds ([The survey](#the-survey-2026-10-26), `init::SUGGESTED_BEACON`), as roadmap decision D8
  did for JSON-RPC (open decision 2): two or more per chain (mainnet: Lodestar, publicnode, then
  the Nimbus team's node in plain HTTP; Sepolia, only sources serving Gloas data: ethPandaOps'
  Nimbus route, the one serving bootstraps at grid roots since the fork, then Lodestar's), all
  taken when Enter alone answers. It recommends them on a public route
  only; on a route to your own node they are an opt-in (open decision 9, below). With one source
  alone (your beacon node, or one public endpoint chosen) the light client runs in **one-source
  mode**, where conflicts across sources and comparison do not hold, and the overview says in
  yellow "from 1 beacon source, no cross-check".
- **Root-only sources** (`beacon_root_check = host,…`) are asked `blocks/{slot}/root` only,
  which every beacon API serves (publicnode's Lighthouse among them), so the first checkpoint
  has two agreeing roots while light-client data comes from one source.
- **On own-node routes** (IPC, TCP on `127.0.0.1` or an onion service, hybrid or not), public
  beacon sources are an opt-in (open decision 9, the user's answer of 2026-10-27; [as
  built](#lc9-own-node)). `lkd init`'s fourth question and `lkd settings`' Light client part
  recommend none there. Before the menu they say what public beacon endpoints cost on such a
  route, `init::OWN_NODE_NOTICE`: "tor starts unless the wallet runs it already, and the beacon
  endpoints see when an lkd light client is online, never your addresses: about 7,200 small polls
  a day while the wallet runs" (open decision 24's routine poll; on the direct route,
  `OWN_NODE_NOTICE_DIRECT`: from this IP, seen by your DNS resolver and your network too).
  Choosing them asks `Use public beacon endpoints? [y/N]` after the notice said again, Enter
  alone no; the review of `lkd settings` and of the window says it once more when the route
  moves from public endpoints to your own node with public beacon sources kept. Otherwise your
  own beacon node (not over IPC), or no light client: balances and nonces proved as before,
  "(proved at block N of your node)" (in hybrid mode at the block the public endpoints agree
  on). A configured public beacon source on the Tor route (an onion beacon node always) makes
  `uses_tor()` true (`crates/launch/src/config.rs`, `Config::uses_tor`), so a wallet whose node
  is reached over IPC or TCP still starts tor; over IPC, netd's view then holds tor's SOCKS
  directory beside the node's, as hybrid mode's does ([`06-tor.md`](06-tor.md)).

**netd's arguments (LC6a; `lkd` passes them from the configuration, LC6c).** `--beacon
127.0.0.1:<port>`, your beacon node on loopback, or `--beacon onion:<port>`, your node's own
onion service (`--onion`) at the beacon node's port, as `lkd` passes `beacon = onion` (netd also
takes `--beacon <56 base32 digits>.onion:<port>`, any onion service); `--beacon-public
<host>[/<path>]`, once per public source, its beacon API under `<path>` (`egress::path_ok`, `/`
when none), over TLS, or `--beacon-public http://<host>[/<path>]` in plain HTTP (`--public
http://…` is refused); `--beacon-direct <path of lkd-beacon>`, the public ones on the direct
route (decision 28: netd starts that `lkd-beacon` before its sandbox and forwards to it; they
then need no tor); `--salt 0x<64 hex digits>` (the `0x` optional), this install's salt
(open decision 11), which `lkd` passes only when a beacon source is configured. The sources are numbered as `lkd-lc` names them: your beacon node first,
when there is one, then the public ones in the order given; every source answers every kind. A
beacon node on loopback is reached on the TCP route only (`--rpc-port`); on the IPC and onion
routes, and with public endpoints and no node, netd's network namespace is empty, so its
requests fail `Unreachable` without a connection being tried, and netd's ready line says why. An
onion beacon node or a public source needs `--tor-socks`, `--tor-control` and `--tor-cookie`;
netd then opens tor's SOCKS socket only (no control connection for beacon sources alone), and
its view holds tor's SOCKS directory. netd's ready line lists the sources by number.

### Several sources, compared (G1, G3)

- **Routine poll** (open decision 24): `finality_update` once a slot, from one source in
  rotation, 4 s into the slot (3 s under Gloas). About 7,200 requests and 15 MB a day
  (*estimate*).
- **Every source** is asked once an epoch, before any refresh the user asks for, and when one
  source's verified update, or its unverified claim (which only triggers a fetch), is more than
  an epoch newer than another source's last answer, to tell a lagging source from a withholding
  one. So the store lags an honest source by at most about an epoch.
- `optimistic_update` only for a source whose finality updates lag; e2e-lc-live checks that
  Lodestar and Nimbus serve the highest attested slot in `finality_update`.
- Updates byte-identical to one already verified skip BLS.
- **Work budget**: each tick verifies a bounded number of BLS checks, cheap checks first.
- A source whose bytes fail a check, or that claims what it cannot back, is marked faulty for
  that round and named in Settings.

### Egress v8 (invariant 10i)

A restatement of invariant 10, extending 10a, 10d, 10e, 10f and 10g, which needs a second
reviewer. Numbered egress v6 and 10g on `feat/light-client`, until prices landed in master as
egress v6, 10g (`18-prices.md`); egress v7, 10h, is the approvals' ([`20-approvals-typed-data.md`](20-approvals-typed-data.md)).

**The `Beacon` class.** `GET` only, with only the `Host`, `User-Agent` and `Accept` headers and
no body (the `User-Agent` is netd's one, `egress::USER_AGENT`, curl's, as on every request netd
writes since decision 27; right after `Host`, where `http::head` puts it), to a configured beacon
source: an endpoint and a scheme, TLS or plain HTTP (below). Every path
is written by `request_bytes` from typed numbers and roots (a 32-byte root in lower-case hex,
decimals), so `path_ok` (`egress.rs:599-618`) stays as
it is, without queries; the `updates` path is the one path with a query, written whole by the
proved function: `light_client/bootstrap/0x{root}`;
`light_client/updates?start_period={p}&count={c}`, `c` from 1 to 14; `light_client/finality_update`; `light_client/optimistic_update`;
`blocks/{slot}/root`, for `--propose` only, and the only path a root-only source is asked.

**EL methods, typed:**

| Request | Isolation group |
|---|---|
| `eth_getBlockByHash(h, false)`; `eth_getBlockByNumber(N, false)` for the head cross-check | `Head` |
| `eth_getProof(a, [], {"blockHash": h})` | `Account(a)` |
| keys `Pin(i)`: pin `i`'s contract and `pin_slots` (its proxy's implementation slot, then its conditions'); `PinImpl(i)`: its pinned implementation's account, no slot | `Shared` |
| keys `Token { index, owner }`: the token's pin's contract and `token_slots` (the owner's balance slot, then the pin's slots) | `Account(owner)` |
| keys `PoolHead(i)`: pool `i`'s pin's contract and `head_slots`; `PoolRoot { index, at }`: the one `root_slot` of head value `at` | `Shared` |
| keys `History(N)`: EIP-2935's contract and `history_slot(N)` (`N mod 8191`), for G9's reorg check of a shared batch's block (allocated for D25, LC9's D38; on `Head` it would share the circuit of the head cross-checks that follow an address's `Account` answers) | `Shared` |
| keys `HistoryFor { number, tx }`, `eth_getBlockByHash(hN, full)` (with its transactions, or its header alone past `MAX_BLOCK_BODY`), `eth_getBlockReceipts(hN)`, for G12 | `Broadcast(n)`, `n` the transaction's broadcast number as for a `Receipt`; by hash only, the transaction's hash never in the parameters |

The module doc of `egress.rs`, which still said "v3", is v8's (done in LC6a, as v6).

**As built (LC6a).** `lkd_verified::beacon` writes the paths: a typed `beacon::Request`
(`Bootstrap { root }`, `Updates { start_period, count }`, `FinalityUpdate`, `OptimisticUpdate`,
`BlockRoot { slot }`), `beacon::path` (`/eth/v1/beacon/` then the request's part, the root as
`0x` and 64 lower-case hex digits, numbers in decimal with no leading zero, `updates` the one
path with a query, written whole), `beacon::request_ok` (a count of 1 to 14) and
`beacon::put_accept` (`application/octet-stream`, `application/json` for `blocks/{slot}/root`).
`egress::beacon_bytes(configured, target, request)` returns, only when `egress::beacon_allowed`
holds (the target is the configured source, which is a beacon node on a nonzero loopback port,
an onion service on a nonzero port or a public endpoint `public_ok` takes, never `Ipc`, and the
request keeps `request_ok`), exactly `GET ` ‖ the source's path without a trailing `/` (public
sources only) ‖ `beacon::path` ‖ ` HTTP/1.1\r\nHost: ` ‖ the host (`127.0.0.1:<port>`,
`<onion address>:<port>`, or the public host) ‖ `\r\nUser-Agent: ` ‖ `egress::USER_AGENT` ‖
`\r\nAccept: ` ‖ the media type ‖ `\r\n\r\n`: three headers and no body (two until the merge
with `feat/suggested-endpoints`, 2026-10-26, which gave every request one `User-Agent`). netd sends a beacon source nothing else (`crates/netd/src/beacon.rs`),
a stream through tor opened with `egress::stream(source, Light(src))`, plain HTTP to an onion
service, TLS 1.3 to a public host on 443. The EL methods built here are the first two of the
table: `egress::Request::HeaderByHash(h)`, `eth_getBlockByHash` with `["0x<h>",false]`, in
`Head`, and `Request::ProofByHash { address, hash }`, `eth_getProof` with
`["0x<a>",[],{"blockHash":"0x<h>"}]`, in `Account(a)`, both allowed at a public endpoint (the
head cross-check's `eth_getBlockByNumber(N, false)` is `Request::Header(N)`, in `Head` since
10d); the key sets are LC7's, G12's requests LC8's. Refined in Lean like 10a to 10f
(`Spec.Beacon`, `Refinement.Beacon`, `Spec.Egress` v8; [`INVARIANTS.md`](INVARIANTS.md) 10i).

**As built (LC7, lc7-egress; 10i restated, a second reviewer).** The key sets are typed,
`egress::Keys::{Pin(u16), PinImpl(u16), Token { index, owner }, PoolHead(u16), PoolRoot { index,
at }, History(u64), HistoryFor { number, tx }}`, and `Request::StorageByHash { chain, keys, hash }`
is `eth_getProof(contract, slots, {"blockHash": hash})` with exactly the contract and slots
`pins::keys_of(chain, keys)` derives (params `["0x<contract>",["0x<slot>",…],{"blockHash":"0x<hash>"}]`,
`[]` for no slot), allowed only when `chain` is netd's and the chain's table has what the key
set names (an index the table lacks, the implementation of a pin with no proxy, a head value out
of its layout's range: refused, nothing sent). `lkd_verified::pins` is the light client's table in
Rust, transcribed separately from this spec's text and refined against `LkdLc.Pins`
(`Refinement.Pins`, D16): the three chains' tables equal row by row, and each derivation
(`pin_slots`, `token_slots`, `head_slots`, `head_value`, `root_slot`, `history_slot`, `plus`,
`mapping_slot`, `balance`, `verdict`, `keys_of`, the lookups by index and by contract) the Lean
one of the same name on every input. G12's `Request::BlockByHash { block, tx, full }` and
`BlockReceipts { block, tx }` are `eth_getBlockByHash(block, full)` and `eth_getBlockReceipts(block)`:
`tx` only names the circuit. The group of each is the table's: `keys_group` from the key set,
`Broadcast(n)` for G12's two. `third_party_ok` refuses a public endpoint only a block by number
with its transactions: D4's commit lets the two G12 requests and the `HistoryFor` read go to a
public endpoint as to your own node, together (`06-tor.md`'s exception; a no to D4 reverts that
commit). netd (`rpc.rs`): `Public::number` gives the G12 requests and a
`HistoryFor` read the transaction's broadcast number, as a `Receipt` gets it (a new one for a
transaction it did not broadcast); `Node::storage_by_hash`, `block_by_hash` (`null` is `None`)
and `block_receipts` send them; the two G12 requests are capped at `MAX_BLOCK_BODY`, and an answer
past its cap is `Failure::TooLarge` (the channel's `TooLarge`, 7; the UI's malformed answer), over
HTTP (`http::Error::TooLarge`) and over IPC. netproto gains `HeaderAt(N)` (`0x20`) and
`Header` (`0x94`, 1 to 2,048 bytes) for the head cross-check (D35): netd's
`Upstream::header_at(N)` asks `Request::Header(N)` of your node or of the public endpoints in
turn, on `Head`, and answers the header's RLP as `reads::header_rlp` re-encodes it, which must
hash to the hash its endpoint gave (else that endpoint's answer is malformed and the next is
asked). `Spec.Egress` mirrors it ([`INVARIANTS.md`](INVARIANTS.md) 10i).

**Plain HTTP (restated 2026-10-26, a second reviewer).** A public beacon source may be reached
in plain HTTP, `http://host[/path]` in `beacon_public`; EL endpoints, relayers, the ASP and price
reads stay TLS only. `egress::BeaconSource` is an `Endpoint` and a `Scheme` (`Tls`, `Plain`):
your own node is `Plain` (on loopback, or inside tor's onion service, which tor encrypts end to
end), a public endpoint either; `beacon_allowed` compares both with the configured source's and
refuses TLS to your own node and anything over IPC. The bytes are `beacon_get` of the endpoint,
the same `GET` in either scheme (`Spec.Beacon.beaconBytes_scheme`). `egress::beacon_stream`
opens the stream: TLS exactly when the scheme is (`stream_tls_iff`); a TLS source as
`egress::stream` reaches a public endpoint (through tor to its host on 443, then TLS); a plain
public source through tor to its host on port 80 (`egress::HTTP`, `Spec.Egress.http`) with the
credentials of `Light(source)` for that host and port, then no TLS (`stream_plain`); your node as
before. `Endpoint` itself has no scheme, so `egress::stream` to a public endpoint is TLS or
nothing (`Spec.Egress.public_never_plain`): no other class can be sent in plain HTTP, by type.
netd builds a source only when `beacon_stream` opens the kind its transport speaks (plain on a
`Tor` stream, TLS on a `TorTls` one) and asks it again at each exchange; a plain source's answer
is read by the same HTTP parser, with the same caps and the same 8 s deadline.

Why it is sound: every light-client object is checked by its hash, its branches and the
committee's signature (25a to 25f), the EL header by its hash and the proofs under its state
root, so a source, a tor exit or anyone behind the exit that alters the bytes can only make
`lkd-lc` refuse them, which stalls or slows the wallet, as a source withholding already can
(H_live); G1 to G8 hold unchanged. What plain HTTP gives up is confidentiality from the exit to
the source: the exit and the network behind it see the request's path, a grid root or a
`start_period` (which say which period's checkpoint a wallet follows, as the source sees anyway),
and public chain data in the answer. No redirect is followed, in either scheme: a `3xx` is the
source's answer and fails `Node`, its `Location` never read, so an HTTPS alias that redirects
to plain HTTP (`ethereum.operationsolarstorm.org`, which sends you to the Nimbus node) is not a
way to reach anything; name the plain source itself.

**netd's behaviour per request (LC6a).** One endpoint is asked per request; `lkd-lc` asks again,
with `attempt` one more for an EL read, after a failure.

| Request | Where it goes | Circuit | Deadline | Failures |
|---|---|---|---|---|
| `ElHeader(attempt, h)` | Your node when the route has one (source 255); else the public endpoint `endpoint_for(h, salt, attempt, n)` picks (its place) | `Own`; at a public endpoint `Head` | 12 s | `NotFound` (`null`), `Node` (an error, a header whose RLP does not hash to `h`), `TooLarge` (over 2,048 bytes), `Unreachable` (no answer within the deadline, an HTTP status but 200), `Denied` |
| `ElProof(attempt, h, a, 0)` | The same, by `endpoint_for(a, salt, attempt, n)` | `Own`; at a public endpoint `Account(a)` | 12 s | `Node` (an error, a proof not for `a`, account fields past 64 or 128 bits), `TooLarge` (over one page), `Unreachable`, `Denied` |
| `Bootstrap`, `Updates`, `FinalityUpdate`, `OptimisticUpdate`, `BlockRoot` (`source`) | The source named, your beacon node first then the public ones; a source not configured is `Denied` | `Light(source)` over tor, TLS or plain HTTP as the source's scheme says; a loopback node directly | 8 s | `NotFound` (404), `NotSsz` (JSON of a version without types here), `Node` (another status, a redirect (`3xx`, never followed) included, a body not of the shape asked, no or a malformed fork name, `Content-Type` neither SSZ nor JSON), `Unreachable` (no answer within the deadline, 403 or 429, a loopback node on a route that cannot reach it), `TooLarge`, `Denied` (`count` outside 1 to 14 is refused by the channel's decoder first, `Malformed`) |

**Isolation.** A new group per source, `Light(src)`, `src` the source's place in the
configuration. Its password text has a fixed length and the first letter `l` of its own
(`isolation.rs:19-20`; "beacon" would clash with "broadcast"); `decodeGroup` gains one case.
A beacon request names nothing about the user's accounts. Built: `light ` and `src` in three
decimal digits (`light 000` to `light 255`), 10c restated. netproto has no `Light` group yet
(its `Group` is what the UI shows), so `lkd network traffic` lists a beacon request as `beacon
<path> @<source>` in the shared group; a netproto variant and its words are the UI track's.

**Caps and paging.** netd's HTTP cap stays 1 MiB (`http.rs:20`), which `count ≤ 14` respects in
SSZ and in JSON; block bodies and receipts take `MAX_BLOCK_BODY`, 8 MiB. Built: since 14 JSON
updates are about 810 KB (58 KB each, measured), close to 1 MiB, an `/updates` answer is read up
to `MAX_RESPONSE` − 1 bytes (netd's `beacon::MAX_UPDATES_BODY`) instead, the count staying 1 to 14, and
`lkd-lc` pulls it in the channel's 60 KiB pages (14 periods of SSZ are about 380 KB, 7 pages);
every other beacon answer is capped at 1 MiB. netd answers each page
request with one datagram of at most 60 KiB (25q). The evidence never crosses a frame: only
`lkd-lc` reads it. lcproto frames are at most 64 KiB, as netproto's
(`crates/netproto/src/lib.rs:12`). `Plan` caps each kind again (proposed: bootstrap 32 KiB, an
update chunk 28 KiB, finality and optimistic updates 4 KiB; fixed in LC6), within the frames'
caps: a channel response of at most 8 MiB, an EL header of 2 KiB, a proof's response of one
page (LC6-0, [Frame layouts](#frame-layouts)).

### The direct route (decision 28)

**Decided by the user on 2026-10-26 ("Beacon only, opt-in"), built on `lc6/beacon-direct`, with
a second reviewer for egress 10i as restated here and for `lkd-beacon`'s sandbox (26c).** One
key, `beacon_route = tor | direct`, `tor` when absent: with `direct`, the public beacon sources
(`beacon_public`, over TLS or in plain HTTP) are reached over this machine's own network, not
through Tor, for speed and because Cloudflare, in front of several public beacon APIs, refuses
many Tor exits. Tor turned off for everything (`route = direct`, `lkd --no-tor`,
[`06-tor.md`](06-tor.md#tor-off)) sends public beacon data this way too, whatever the key says,
and Settings then hides the choice. Nothing else moves: your own beacon node is reached as before (loopback, or its
onion service), and EL reads, broadcasts, relayers, the ASP and the price reads stay on Tor or
your own node. The light client checks every object as before, so the route changes privacy and
speed, never what is accepted.

**`lkd-beacon`, a process of its own.** netd carries your addresses, so it keeps its empty
network namespace (19a): the direct connections are made by `lkd-beacon`, a second, small binary
of `crates/netd` (`src/bin/lkd-beacon.rs`), which only ever receives typed beacon requests (a
source's number and a `beacon::Request`: a block root, period numbers, a slot) and returns the
source's HTTP answer. It holds no key, no address, no configuration of yours beyond the public
sources' names, and reads no file once sandboxed. A beacon-only mode of `lkd-netd` was weighed
and not taken: the networked process would carry the whole of netd (the JSON-RPC client, the
UI's server, tor's control client) where it needs four of its modules (`http`, `tls`,
`deadline`, `direct`), and its arguments and sandbox would be netd's with one more mode to get
right. A separate binary has its own `main`, which has no path to anything of the user's.

**Who starts it.** netd, before its own sandbox, when `lkd` passes it `--beacon-direct <path>`
(the `lkd-beacon` next to `lkd`), which `lkd` does only when `beacon_route = direct` and at least
one public beacon source is configured, or when Tor is off (`route = direct` or `lkd --no-tor`,
[`06-tor.md`](06-tor.md#tor-off): no tor runs, so public beacon data takes this route whatever
`beacon_route` says; `Config::beacon_route_direct`). netd makes a Unix stream pair (std's
`UnixStream::pair`), starts `lkd-beacon` with one end as its standard input, an empty
environment, its standard output to `/dev/null` and its standard error netd's (so `lkd` passes
its lines on), and keeps the other end; it waits up to 10 s for `lkd-beacon`'s ready frame. `lkd`
supervises it through netd: `lkd-beacon` ends when netd does (its parent-death signal, and end of
file on its channel, whichever comes first), and netd stops, after the request that finds it
gone, for `lkd` to start it again with a fresh `lkd-beacon`, when the channel of a `lkd-beacon`
that was ready closes or carries what does not read; one that never became ready (the binary
missing, its sandbox refused) leaves its sources `Unreachable` with the reason in netd's ready
line, without netd restarting over a fault a restart does not mend. Why netd and not `lkd`: the channel is then a
descriptor netd makes itself before its sandbox, so no third inherited descriptor (which `lkd`
could pass only with `unsafe` code before `exec`) and no change to netd's view; `lkd-beacon`'s
life is netd's, so there is never a second or stale helper on the channel and no generation to
compare; and a settings change, which already restarts netd, restarts it too. `lkd-lc`, its
channel, its source numbering and the Lean core are unchanged: netd forwards, `lkd-lc` cannot
tell the routes apart. `lkd-beacon` ships beside the other binaries (`paths::BINARIES`, `dist.sh`,
`install.sh`), and `release-check` holds it to no development option.

**The frames** (`lkd_netd::direct`, tested, not proved). Each frame is a big-endian `u32` length,
then the frame. netd sends `id` (`u32`, one more each request), the source's place among
`lkd-beacon`'s sources (`u8`, netd's number less one when your beacon node is source 0), and the
request: `0` and a 32-byte root (`Bootstrap`), `1`, a `u64` start period and a `u8` count
(`Updates`), `2` (`FinalityUpdate`), `3` (`OptimisticUpdate`), `4` and a `u64` slot
(`BlockRoot`), exactly that long. `lkd-beacon` answers `id`, then `0` and the HTTP status
(`u16`), the `Content-Type` and the `Eth-Consensus-Version` values, each a `u8` length and at
most 255 bytes (empty when absent or longer), and the body; or `1`, a channel failure code and
why, at most 200 bytes of UTF-8. Its first frame, id 0, is `2` and its sandbox report: it is
ready. netd waits for each answer within the request's deadline (8 s, `deadline::Bounded`),
keeping a frame it stopped waiting for half-read to finish on the next request, and drops an
answer whose `id` is not the one it waits for (a late answer to a request it gave up on);
`lkd-beacon` gives each request 7.5 s, so that its failure reaches netd in time. Everything netd
did with an answer before, it does with this one: the same status codes, `Content-Type`, version
names, re-encoding and caps (`beacon::answer`), the same traffic log line. A request is at most
38 bytes after its length, an answer at most `beacon::MAX_UPDATES_BODY` and its fields.

**What `lkd-beacon` sends, and where.** It is started with the public sources alone, in netd's
order (`--source [http://]host[/path]`, as netd's `--beacon-public`), each an
`egress::BeaconSource` with `Route::Direct`. For a request it asks the proved policy, as netd does
on the Tor route: the bytes are `egress::beacon_bytes` of that source (the same `GET` on either
route, `Spec.Beacon.beaconBytes_route`), and the connection is `egress::beacon_stream`'s, which on
the direct route is `Stream::ClearnetTls { host, 443 }` for a TLS source and
`Stream::Clearnet { host, 80 }` for a plain one: it connects to exactly that host and port, then
speaks TLS 1.3 (netd's `tls`, the bundled roots, the certificate valid for that host) or plain
HTTP, and reads the answer with netd's `http::send`, the same caps, no redirect followed. It keeps
one connection per source open and opens it again once when a kept one fails before any byte of
an answer, as netd does with its streams.

**Names.** `lkd-beacon` resolves the hosts itself, with a stub resolver of its own
(`lkd_netd::dns`): the `nameserver` lines of `/etc/resolv.conf` (at most three, IPv4 or IPv6
literals; `127.0.0.1` when there are none, as glibc does), read once before its sandbox, asked
over UDP port 53 for `A`, then `AAAA` when there is no `A`, one question at a time, 2 s each,
within the request's deadline, from a socket connected to the server (so the kernel drops
datagrams from anyone else), with a random 16-bit id; an answer counts only with that id, the
response bit, `NOERROR`, the same question, and records for the name or the `CNAME`s the answer
names for it (at most 8). Addresses that are not global (loopback, private, link-local, shared,
unique-local, multicast, unspecified, documentation) are refused, so a resolver cannot point
`lkd-beacon` at a service on this machine or its network. Why not the system's `getaddrinfo`: it
loads NSS modules at run time and may talk to `systemd-resolved` over D-Bus or varlink sockets,
which a sandbox with no files and no `AF_UNIX` cannot allow. Why not DNS over HTTPS: one more
third party, and a resolver of its own to start from. The hosts are public names; what the
resolver learns is which public beacon hosts this machine asks, and when. A forged answer (DNS is
not authenticated) sends `lkd-beacon` to another address: a TLS source's certificate check then
refuses the connection, and a plain source's bytes are checked by `lkd-lc` as every plain
source's are, so it can stall the light client, never mislead it. `/etc/hosts` is not read.

**Egress v8, restated for the route (10i, a second reviewer).** `egress::BeaconSource` gains a
third field, `route: Route` (`Tor`, `Direct`), and `egress::Stream` two kinds,
`Clearnet { host, port }` and `ClearnetTls { host, port }`: a TCP connection over this machine's
network to `host`, which `lkd-beacon` resolves, on `port`, then plain HTTP, or TLS 1.3 for
`host`. `beacon_allowed` compares the route as it compares the endpoint and the scheme, and
`beacon_source_ok` takes `Direct` for a public endpoint only (your own node is `Plain` and
`Tor`). `beacon_stream` is unchanged on the Tor route; on the direct route it is
`ClearnetTls { host, 443 }` or `Clearnet { host, 80 }`, `host` the configured public host
`public_ok` takes, and nothing for any other source. Proved (`Spec.Beacon`, `Spec.Egress`,
`Refinement.Beacon`):

- a direct stream exactly when the route says so: a stream to a beacon source is `Clearnet` or
  `ClearnetTls` if and only if the source's route is `Direct` (`stream_direct_iff`);
- exactly the configured host and port: such a stream is to a public endpoint `publicOk` takes,
  its host the configured host, on 443 with TLS when the scheme is TLS, on 80 without when it is
  plain (`stream_direct`, `code_beacon_direct`);
- only the beacon class: `egress::stream` of any `Endpoint`, whatever the group, never yields a
  `Clearnet` or `ClearnetTls` stream (`Spec.Egress.stream_never_clearnet`,
  `Refinement.Beacon.code_stream_never_clearnet`), so JSON-RPC, broadcasts, relayers, the ASP
  and the price reads, which open their streams through `stream`, go through tor (or to your own
  node) whatever the setting, the analogue of `public_never_plain`;
- only for a configured public source: a request is allowed only to the configured source,
  route included, and a direct source must be public (`beaconAllowed_iff`, `sourceOk_iff`); in
  one statement, an allowed request whose stream is direct goes to the configured source, whose
  route is `Direct`, a public endpoint, its host on the scheme's port (`allowed_direct`);
- TLS still exactly when the scheme is TLS, on either route (`stream_tls_iff`), and the bytes
  the same on either route and in either scheme (`beaconBytes_route`, `beaconBytes_scheme`).

Not proved: that `lkd-beacon` connects to the address its resolver gave for that host (reviewed,
tested), and that netd sends `lkd-beacon` only beacon requests (by type: the frame holds a
`beacon::Request` and a source's number, nothing else; tested).

**Live apply.** The window's Privacy form ("Beacon data", shown with public beacon sources: "Through
Tor" or "Directly", what it reveals read before it applies) changes it through `lkd`'s control
socket, as the other privacy settings: `lkd` writes the configuration and starts netd again at
once, which starts `lkd-beacon`, or not; `lkd-lc` keeps running, as through any restart of netd.
An edit that leaves tor unneeded drops a configured `tor` rather than failing. `lkd settings`
(Light client, item 5) changes it in the file, for the next start, after the same notice; its
review says what it reveals. Turning it on starts no tor; turning it
off starts tor if the configuration then needs it. `uses_tor()` counts public beacon sources only
on the Tor route, so a wallet on your node with direct beacon sources starts no tor at all.

**What it costs**, said where it is turned on (Settings, `lkd settings`): each public beacon
source sees this machine's IP polling it once a slot or so, so it can tell that an lkd light
client runs here and when, and so can your DNS resolver and anyone on the path (for a plain
source, the paths too: a grid root, a `start_period`, which say which period's checkpoint the
wallet follows); none of it names your addresses. A compromised netd or `lkd-lc` could, on this
route, send those hosts from your IP data of its choice inside typed requests (a bootstrap's root
is 32 bytes of its choosing): over Tor that reached them without your IP. A compromised
`lkd-beacon` holds nothing of yours to leak.

**Kernel requirements.** `lkd-beacon`'s TCP connections are held to ports 443 and 80 by
Landlock's network rules, Linux 6.7 and later (ABI 4). On an older kernel, or with Landlock off,
they are not: `lkd-beacon` says so in its report (netd's ready line, `lkd doctor`), and it may
then connect to any port, still only by IPv4 or IPv6 (its filter refuses every other socket
family), with no file, and still holding nothing of yours. Its empty file system needs user
namespaces, as netd's view does; without them it says so, and its filter still refuses every
call that takes a path. Abstract Unix sockets and signals are scoped from ABI 6 (Linux 6.12).

### Privacy

- **The checkpoint grid.** A bootstrap names the wallet's checkpoint; a root chosen at an
  arbitrary moment would mark one wallet across sessions. Checkpoints are taken on a grid: the
  block at a period's first slot, or the last before it when that slot is empty, once
  finalized. That is an epoch checkpoint root, which Lighthouse requires for a bootstrap. Every
  `lkd` started that period shares it, and every running `lkd` fetches a grid root's bootstrap
  in the same epoch ([Refresh](#refresh)).
- **The catch-up request at a start** is the same for every `lkd`; its timing says a wallet
  started.
- **Circuits**: one `Light(src)` group per source. Proofs are asked by hash at the anchor,
  the same block for every `lkd` at that moment. Account proofs go on `Account(a)`, as
  `eth_getBalance` does today, each address to the one endpoint kept for it, so an endpoint
  learns only its share of addresses (open decision 11). All pinned tokens are asked for the
  selected address, so the request does not say which tokens it holds; pins on `Shared`,
  whatever the user holds; G9's history proofs on `Shared`, by number only, with the pin and
  pool batches whose blocks they check (LC9's D38), never on `Head`, whose cross-checks follow an
  address's reads; G12's requests in the transaction's group, which already knows it.
- **Polling** marks a light-client user and its timing, the same for every `lkd`: beacon
  endpoints see over Tor that an lkd light client is online and when, never its addresses.
- **A plain-HTTP source** shows the same to the tor exit and the network behind it: the paths
  (a grid root, a `start_period`, a slot), which say which period's checkpoint a wallet follows,
  and the public answers. They name nothing of the user's, travel on `Light(source)`'s circuits
  only, and the source sees them anyway; what is lost is that the exit no longer learns only a
  host name. An exit can also alter or withhold the bytes, which only stalls the wallet.
- **The direct route** (`beacon_route = direct`, decision 28, or Tor off): the public beacon sources, your
  DNS resolver and the network between see this machine's IP poll them, so that an lkd light
  client runs here and when (for a plain source, the paths too). The requests are the same bytes
  as over Tor and name nothing of yours; they come from `lkd-beacon`, which never holds anything
  of yours. Your own beacon node, the EL reads, broadcasts, relayers, the ASP and the price reads
  are not on this route.

### The survey (2026-10-26)

Done over plain HTTPS from one machine, two providers per fact (the full report, raw answers and
scripts are kept out of the tree, in `.tools/scratch-lc/survey/`), then over Tor at LC9's
integration (below).

**Beacon sources.** Each source in the table serves the four light-client endpoints over TLS in
the one profile `tls_handshake` speaks.

| Chain | Source | Answers | Notes |
|---|---|---|---|
| mainnet | `lodestar-mainnet.chainsafe.io` (Lodestar) | SSZ | Bootstraps at every grid root back to Altair; its `finality_update` lags the head by up to 10 slots; 429 on bursts of block-root lookups |
| mainnet | `ethereum-beacon-api.publicnode.com` (Lighthouse) | JSON only | netd re-encodes it for Electra and Fulu (LC6a) |
| Sepolia | `beacon.sepolia.ethpandaops.io/nimbus` (Nimbus behind dugtrio) | SSZ, Gloas | The one source serving bootstraps at grid roots since the Gloas fork; without the `/nimbus` prefix requests reach Prysm, which serves none |
| Sepolia | `lodestar-sepolia.chainsafe.io` (Lodestar) | SSZ, Gloas | Answers 500 for a bootstrap at any grid root since the fork; lags up to 32 slots; 429 to 6 parallel requests |

Usable since plain HTTP is allowed for beacon sources (2026-10-26): the Nimbus team's mainnet
node, `http://testing.mainnet.beacon-api.nimbus.team` (Nimbus v26.10.2: all four endpoints in SSZ,
full history, `finality_update` within a slot of the head; port 443 refuses connections, and
`https://ethereum.operationsolarstorm.org` answers a 301 to it in plain HTTP, which netd never
follows). Checked live from this machine, not over Tor, on 2026-10-26: its `finality_update` (2,106
B, `fulu`) decodes in `LkdLc`, its finality branch checks, 512 of 512 signed, and it is accepted
by `Store.receive` under the committee of a bootstrap the node served at the update's finalized
root, a root Lodestar answered too for that slot; one flipped signature byte is `badSignature`.
`lkd init` suggests it third on mainnet. Not usable: the Nimbus team's other nodes
(`unstable.…`, a shorter history; Sepolia's, not suggested since ethPandaOps serves the same
Nimbus over TLS); every Checkpointz server (no
light-client data; their block roots come without `0x`, recent checkpoints only, so the
assumption that every source serves `blocks/{slot}/root` does not hold); publicnode on Sepolia
(no Gloas data); ethPandaOps' Lighthouse route on Sepolia, which has served one update labelled
`gloas` with a Fulu-shaped header since the fork (kept as a test vector for G8). `lkd init`
suggests the four sources above and the Nimbus team's mainnet node (`crates/launch/src/init.rs`).
Mainnet thus has two SSZ sources (one over TLS, one in plain HTTP) and one JSON one; Sepolia two
SSZ sources, one of which can give a first checkpoint.

**Over Tor (2026-10-27, LC9's integration: `lkd-e2e --lc-survey`, curl with netd's
`User-Agent` through a tor of the harness's own, read-only, no wallet).** Every suggested source
and endpoint answered over Tor, each its own circuit:

| Chain | Source or endpoint | Over Tor |
|---|---|---|
| mainnet | `lodestar-mainnet.chainsafe.io` | the bootstrap at the grid root (slot 15,523,840, 25,672 B), `updates` and `optimistic_update` in SSZ; its `finality_update` timed out once at 8 s on the survey's circuit and answered in SSZ (2,106 B) on the live run's; `finality_update` fulu |
| mainnet | `ethereum-beacon-api.publicnode.com` | all four in JSON only (netd re-encodes Electra and Fulu) |
| mainnet | `http://testing.mainnet.beacon-api.nimbus.team` | all four in SSZ, in plain HTTP over Tor |
| mainnet | dRPC, 0xRPC, MEV Blocker | `eth_getProof` by `blockHash` at the finality update's attested (26,286,781) and finalized (26,286,715) blocks |
| Sepolia | `beacon.sepolia.ethpandaops.io/nimbus` | all four in SSZ, `gloas` |
| Sepolia | `lodestar-sepolia.chainsafe.io` | 500 for the bootstrap at the grid root (slot 11,444,224); `updates`, `finality_update` and `optimistic_update` in SSZ, `gloas` |
| Sepolia | ethPandaOps, 0xRPC, OnFinality | `eth_getProof` by `blockHash` at the attested and finalized headers' `execution_block_hash` (Gloas: the parent payload's); OnFinality answered 429 (`-32029`, "Too Many Requests") at the finalized one in the live run's survey |

`blocks/{finalized slot}/root` answered on each source that serves it, the same root on every
one. So To confirm 6 is answered over Tor, as LC9's live run used it: mainnet has three sources,
two in SSZ, and Sepolia two, of which ethPandaOps' Nimbus route alone serves a bootstrap at a
grid root.

**EL endpoints, proofs by block hash at the anchor.** Mainnet: dRPC, MEV Blocker, Blast API
and 0xRPC answered every probe; publicnode 14 of 16 (reth's proof window, behind a load
balancer); Tenderly with 32-byte keys only; Flashbots Protect refuses. Sepolia: ethPandaOps,
OnFinality, 0xRPC and Tenderly answered every probe; 1RPC 7 of 11; publicnode and dRPC none.
So the anchored proof needed the attempt counter's retry on another endpoint, while the
suggested EL lists (`lkd_ctlproto::SUGGESTED`) put first, on Sepolia, two endpoints that never
prove at the anchor. Resolved by decision 27 (2026-10-26): the lists now hold only endpoints
that proved at the anchor over Tor on every exit tried, on Sepolia ethPandaOps, 0xRPC and
OnFinality, on mainnet dRPC, 0xRPC and MEV Blocker, each request with one fixed `User-Agent`.

**Storage layouts and pins (LC7).** Every slot and code hash LC7 needs was found and checked
against the getter's `eth_call` at one block on two providers: the four mainnet tokens' balance
slots (USDC 9 with bit 255 its blacklist flag, masked; USDT 2, with `deprecated` and
`upgradedAddress` in slot 10 as its storage condition; DAI 2; WETH 3), USDC's implementation at
the ZeppelinOS slot, Sepolia's WETH 3 and LINK 0, Tornado's `currentRootIndex` and roots,
Privacy Pools' `currentRoot` and the Entrypoint's `latestRoot` and `assetConfig`, and EIP-2935's
history slot rule (still holding on Sepolia under Gloas). Two facts change LC7's design: a pool
root and `latestRoot` each need two storage keys in one proof (one value locates the other),
and the pools run linked libraries and verifiers whose code hashes are pinned too.

## The checkpoint and the evidence

### The first checkpoint

**As decided on 2026-10-28** (open decision 29; this restates what follows where they differ).
The light client is on by default on public routes: a configuration with `node = public`, no
beacon source and no `light_client = off` gets the chain's suggested public beacon sources and a
salt at `lkd start`, written once and said once on `lkd`'s terminal and in the wallet. On a route
to your own node it stays an opt-in (D53): Networks' toggle turns it on there, with the notice.
The checkpoint step no longer holds the start: `lkd` holds `lkd-lc` stopped and runs `--check`
then, when needed, `--propose` on a thread of its own while keyd asks for its passphrase and the
UI starts, and never reads the terminal for it (17c). `--propose` prints `proposed <root> <slot>
<time> <k> <n>` (`n` the configured sources) when every source that answered named the root, at
least two, and otherwise `offered` with the root the most named (the first source's on a tie),
its bootstrap verified the same way. Either waits for that bootstrap at most 60 s per source
(200 s in all), and no longer once every source answered that it has none (not found): a
disagreement whose offered root no source serves then says so at once rather than holding
`lkd-lc` stopped to the deadline. **The rule** (`lkd`'s `checkpoint::choose`): a `proposed`
root with `k = n ≥ 2` is written without a question, `checkpoint_from = unanimous:<n>`, said on
`lkd`'s terminal with where to compare it; any other root (`offered`, a source that did not
answer, or any root once the store halted on a conflict) is not written: `lkd` asks the wallet
(`Request::Light`'s `Asking`: the root, its slot and time, how many of the configured sources
named it, what each said), and writes it only on Take this checkpoint (`Request::Checkpoint`,
the very root asked about: `agreed:<k>/<n>`); Not now leaves the light client off until the
toggle or the next start, which asks the sources again (no weekly memory of a decline any
more); nothing proposed is "no checkpoint yet", asked again from Networks. `lkd settings
--propose` follows the same rule, asking on its terminal instead. What this trusts: the
sources' word on first use, with no comparison by default; the bootstrap's checks are
unchanged.

At `lkd start`, before `keyd` asks for its passphrase (so 17c holds), when no checkpoint is
set, or the store is past `MAX_AGE` ("the light client's checkpoint is too old: a new one is
needed") or halted:

1. `lkd` runs the sandboxed one-shot `lkd-lc --propose` with the channel's end and the
   evidence's descriptor, after waiting up to 60 s for tor's bootstrap. It says "Light client:
   asking 2 beacon sources over Tor for the block that starts sync period P (slot S, <date>)…",
   with tor's progress, waits at most 60 s per source, and names any that did not answer. The
   whole step, tor's bootstrap included, is timed in LC6 and its expected length printed.
2. `S` is the newest period start at least 3 epochs before the clock, stepping back past empty
   slots at most 32 slots; past that it says the sources have no block there and the clock may
   be wrong.
3. **Every** source that answers `blocks/{S}/root` (JSON, untrusted), light-client and
   root-only alike, at least two, must agree.
4. It fetches and verifies that root's bootstrap (`hash_tree_root`, the committee's branch,
   KeyValidate) and persists it in the evidence.
5. It writes the root on its pipe; `lkd` parses it and prints: "Checkpoint 0x1a2b 3c4d …
   (slot S, <date>): 2 of 2 sources agree. Compare it with the block root of slot S on an
   explorer (beaconcha.in/slot/S, sepolia.beaconcha.in/slot/S) or with `curl <your beacon
   node>/eth/v1/beacon/blocks/S/root`. Type yes if it is the same, no to skip."
6. On yes, `lkd` writes `checkpoint = 0x<64 hex digits>` and `checkpoint_from = agreed:<k>/<n>`
   through `lkd-verified`'s `config`, extended beyond `chain_id` with a round-trip proof (25e).

"2 of 2 agree" is the sources' word, carried by netd: only the user's comparison outside the
wallet stands against a compromised netd or colluding sources (H_cp). On a disagreement each
source's root is printed in red, yes is not offered, and the overview says so. On a decline or
a skip the wallet runs on the yellow path, the overview says "Light client off: no checkpoint
set (lkd settings → Light client)", and the question comes back at most once a week; a root can
be typed in `lkd settings` (`checkpoint_from = typed`). There is no compiled-in default and no
fallback: a release ages past `MAX_AGE`. After "too old", `--propose` also replays the old
evidence with the bound lifted and says whether the proposed root is reached from the previous
checkpoint, and, when every source's claimed head is far behind the clock, "your clock may be
ahead": hints only, never a substitute for the user's comparison.

**As built (LC6, `lc6/ui`: `crates/launch`).** The configuration keys, read and written by
`lkd`'s parser (`crates/launch/src/config.rs`), the roots through `lkd_verified::config`'s
`format_root` and `parse_root`, proved to round-trip (25e): `checkpoint = 0x<64 lower-case hex
digits>` with `checkpoint_from = typed | agreed:<k>/<n> | refreshed` (required with it) and
`checkpoint_slot = <slot>` (when known: proposed or refreshed; the date, epoch and age shown are
computed from it on mainnet and Sepolia); `beacon = 127.0.0.1:<port>` (not with `node = ipc`) or
`beacon = onion:<port>` (with `node = onion`, the node's own service); `beacon_public =
host[/path],…` (at most 8, checked as public endpoints are); `salt = 0x<64 hex digits>` (random,
written by `lkd init` for every install, and once by `lkd settings` or `lkd start` for an install
with beacon sources and none, such as one made before the light client). The window cannot change any of them; a network change
drops all but the salt. `lkd init` asks a fourth question on mainnet and Sepolia: public beacon
endpoints (suggested per chain, pending the survey), your beacon node, or none; then the
checkpoint pasted, or taken at the first start (recommended). `lkd start`, after netd and before
`lkd-lc` and keyd, runs `lkd-lc --propose` when sources are configured and no checkpoint is set
(not within a week of a decline, kept in `<home>/lc/<chain>.declined`), prints the root grouped by
four with its slot, date and agreement and where to compare it, and writes it only on `yes`
typed; with a checkpoint set it runs `lkd-lc --check` and writes the reached grid root,
`refreshed`, when it is more than a week newer, or proposes anew on `stale`. `lkd settings
--propose` and `--check` do the same while the wallet is stopped (`--propose` starts tor and netd
for the one-shot; `--check` asks before moving). The one-shots' command line and output lines
are an interface `lkd` defines (`crates/launch/src/checkpoint.rs`): `grid`, `source`, `proposed`,
`checked`, `none`, `stale`, `hint`. Not built here: root-only sources (`beacon_root_check`) and
`lc_clear_conflict`.

**As integrated (LC6, `lc6/integrate`: `crates/lc`, `lkd_lc::oneshot`).** Both one-shots start as
the daemon does, in its order and sandbox, without its socket; `--check` takes no channel even when
standard input is one. Each prints its lines and exits 0.

- `--propose`: the grid slot from the chain's slot schedule (`LkdLc.Forks`' mainnet and Sepolia,
  or `LkdLcDev`'s with the development genesis), repeated in Rust; `BlockRoot(i, S)` asked of
  every source at once through the channel (under tags from 2³¹, apart from the core's), 60 s for
  their answers; stepped back past slots every source answered empty (404), at most 32; then
  `grid` and each `source`. The requests are the core's (`Plan.proposeAsks`, through
  `lkd_lc_propose_asks`) and the root is taken by the core's rule (`Plan.proposeRoot`,
  `Plan.proposeAgreed`'s: at least two answered, every one that did names it, through
  `lkd_lc_propose_agreed`; Rust only words why nothing was agreed); with no source configured it
  says `none` at once. Since 2026-10-28, when the rule takes none, the root the most sources
  named (the first source's on a tie; Rust, `oneshot::offered`) is started from instead and
  printed as `offered`, the rule's reason as a `hint`: only the user's yes takes it. The core is then started again from that root (the runtime
  was started before the sandbox, with no checkpoint), given the evidence's copies (so a write
  goes to the inactive one under the next sequence) but not the conflict block, which is the
  daemon's to check, and run until the bootstrap verified and a copy holding it was written, or
  the evidence held it already and it verified again: at most 60 s a source, 200 s in all. Only
  then `proposed 0x<root> <slot> <time> <k> <n>`, `n` the configured sources (`<k> <k>` before
  2026-10-28), or `offered` with the same fields.
- `--check`: `Load` with the copies and the conflict block, no channel, ticked at once until the
  check ends. `stale` when the phase is halted or too old, or when a copy held the checkpoint's
  bootstrap and none verifies any more (the core asks the bootstrap again: past `MAX_AGE`, or both
  copies damaged); `checked 0x<root> <slot> <time> <updates>` when the core reached a grid
  checkpoint other than the configured one (read from the core's state through
  `lkd_lc_reached`, the slot's time from the chain's schedule; [Refresh](#refresh)); `none`
  otherwise ("the evidence holds nothing from this checkpoint yet", or "the evidence verifies from
  the checkpoint; it keeps no newer grid checkpoint whose bootstrap verified, to move to"). No
  `hint` (the old evidence replayed past `MAX_AGE`) is printed yet.
- Development builds: `lkd start --dev-beacon <file>`, and `lkd settings --propose|--check` with
  `--dev-beacon` and `--test-root`, pass the fake beacon's chain (the generator's `dev` file) to
  every start of `lkd-lc` as `--dev-genesis`, `--dev-gvr` and `--dev-gloas`; `release-check.sh`
  refuses the name in a release `lkd`.

### Refresh

`Load` replays the evidence from the configured checkpoint and applies `MAX_AGE` at every step,
so **the configured checkpoint must be younger than `MAX_AGE` at every start and restart of
`lkd-lc`**: a running `lkd-lc` stays fresh past that point, a restart does not. A refresh moves
the checkpoint forward along verified evidence (open decision 7):

- `lkd-lc --check` reads the evidence, verifies it from the configured checkpoint, and writes on
  its pipe the newest finalized grid root the evidence reaches within `MAX_AGE` whose bootstrap
  the evidence holds, with its slot, date and the number of updates leading there. The launcher
  runs it at every start, in the background while `keyd` asks, and about once a period while
  the wallet runs; it never writes a root on the running daemon's word.
- When that root is more than 7 days newer than the checkpoint, the launcher writes it with
  `checkpoint_from = refreshed`, without reading the terminal, and once `keyd` is ready prints
  "Light client checkpoint moved to slot S (<date>) along verified updates"; Settings shows it,
  and `lkd-lc` uses it from its next start (as built, the very start whose check moved it).
- A checkpoint older than 7 days that no refresh moved is shown on the overview, "refresh
  needed: restart within N days, or a new checkpoint will be needed", red from day 10.

A finalized header is on the grid when its checkpoint epoch, read from
`finality_branch[len − floorlog2(gindex)]`, is a period's first epoch; the evidence keeps the
update that first finalized each period's grid block it saw. `lkd-lc` fetches a grid root's
bootstrap while it is still the current finalized checkpoint, so that sources serving only that
one serve it; checks its committee against the evidence's committee for the period of the
checkpoint block's own slot (the period before, when the period's first slot is empty); and
keeps the newest one or two. When no grid update exists for a period, because finality skipped
its first epoch or `lkd-lc` caught up through period updates, `--check` offers the newest earlier
grid root. A refresh adds no trust: the chain from the old checkpoint to the new one was
accepted by the same code within `MAX_AGE`. `crates/ui/src/settings.rs:5-6` stays true: the
checkpoint is an argument to `lkd-lc`, never decided by the UI.

**As built** (`lc6/refresh`, 2026-10-26: `LkdLc.Evidence`, `LkdLc.Lc`, `LkdLc.Plan`,
`LkdLc.Ffi`; `crates/lc-core`, `crates/lc`; theorems in `LkdProofs.Lc.Refresh` and
`LkdProofs.Lc.Evidence`, 25e, 25h, 25n):

- **Reaching a grid checkpoint.** An update the store accepts (`Store.receive`, so two thirds of
  the current or next committee signed it, within `MAX_AGE`, no conflict) whose finality branch
  proves a checkpoint epoch that is a sync period's first, its finalized header not genesis
  (`Evidence.onGrid`), and whose finalized slot is newer than the store's finalized header before
  it and than the grid checkpoint the evidence keeps or wants (so never the configured checkpoint
  or one older), makes the book want that checkpoint (`Book.reach`). Such an update is proved by
  the store it was received by (`receive_provesGrid`: `Evidence.provesGrid`, `provesGrid_iff`).
- **Its bootstrap.** The planner asks `Bootstrap(source, root)` for the wanted root at once, so
  while it is still the current finalized checkpoint, from one source at a time in rotation, at
  most four times for one root (`Plan.gridCands`, `maxGridAsks`). A bootstrap for that root that
  verifies as a configured checkpoint's would (`Store.bootstrap` for the root at the clock: the
  header valid at its fork, its root, the committee's branch, `MAX_AGE`, KeyValidate), its header
  at the checkpoint's slot, makes it the grid checkpoint the book keeps, persisted at once
  (`Lc.ingestGrid`, a step of the inbox's budget of its own); one that fails marks its source
  faulty for the round. The committee is not compared with the evidence's committee for that
  period (a departure from the text above): the branch binds it to the header two thirds of a
  committee the store holds finalized, and a differing committee would be a conflict two thirds
  signed, which only stops a refresh. Only the newest grid checkpoint is kept; one wanted but
  never served leaves the older one in place.
- **The evidence** keeps it (payload version 2, [the evidence file](#the-evidence-file)); `Load`
  replays the copy as before, then checks the kept grid checkpoint against the loaded store in a
  step of its own (`Evidence.checkGrid`: its update decodes, names the root, is proved by the
  store; its bootstrap verifies for that root at the clock) and keeps it only then
  (`checkGrid_ok`, `advance_grid`).
- **`--check`** prints `checked 0x<root> <slot> <time> <updates>` for the grid checkpoint the
  core keeps once the evidence check is over, when it is not the configured one: `reached`, read
  through `lkd_lc_reached`, reports it only while the store is not halted and within `MAX_AGE`,
  the checkpoint itself younger than `MAX_AGE` at the clock and its bootstrap kept; `updates` is
  the number of updates the evidence replays from the configured checkpoint. `reached_sound` (25h):
  the root and slot are those of a finalized header an update proves as a grid checkpoint against
  a store a run from the configured checkpoint gives, and the kept bootstrap verifies for that
  root at the clock (25e for the start from it).
- **The launcher** (`crates/launch`, unchanged by the refresh): at a start it writes the root,
  its slot and `checkpoint_from = refreshed` when it is more than 7 days newer than the checkpoint
  (on the development chain, whose slots `lkd` does not know, any newer root), and prints "Light
  client checkpoint moved to slot S (<date>) along verified updates"; `lkd settings --check` asks
  first. The overview's "Refresh needed: restart within N days" from day 7, red from day 10, for a
  checkpoint no refresh moved, is the UI's (`crates/ui/src/light.rs`, LC6c).
- **The refreshed start.** With the new root configured, a copy whose grid checkpoint is that
  root is a `Load` candidate whose payload is the kept bootstrap alone (`Evidence.candidate`,
  `moved`; `candidate_moved`): the store starts from it with `Store.bootstrap` for the configured
  root, offline, at the first step and loads at the next (`moved_loads`), and the evidence is
  written at once under the new checkpoint, to the copy not loaded (`tickLight_moved`); the copy
  of the old checkpoint is overwritten at the next write after that. The updates after the grid
  checkpoint are not carried over: the planner's catch-up fetches them again, and the store
  anchors once it has them. Until then it holds the grid checkpoint's committee alone, so a
  snapshot whose update was signed in a later period is `Pending` until the catch-up reaches that
  period ([Frame layouts](#frame-layouts), `Lc.ahead`).
- **Follow-up, not built: replaying the moved copy.** A moved copy could replay the evidence's
  updates after the grid checkpoint as well, so that a restart after a refresh anchors at once,
  offline, as a restart without one does. The payload keeps the updates from the old checkpoint,
  and a store started at the grid checkpoint has no committee for the periods before it: today such
  an update stops the replay (`unknownPeriod`) and fails the copy. It needs `candidate` to keep the
  payload's updates for a moved copy, the replay to skip, after decoding, each update signed before
  the store's period (and only those), `candidate_moved` and `moved_loads` restated (the store
  `Reaches` the configured checkpoint along the updates kept), and the plan test's refreshed start
  and the e2e `lc-refresh` changed to match; it was left out of the snapshot fix as not small.
- **Tested**: `lkd-lc-plan-test`'s refresh scenario (reached, kept, persisted, reported again by
  an offline load as `--check` does, a refreshed start offline that never asks its own bootstrap
  again, sources serving no grid bootstrap); the e2e `lc-refresh` (the wallet running past a period's first epoch, the next
  `lkd start` moving the checkpoint, `lkd-lc` starting from the kept bootstrap without asking it
  again, anchoring).

### The age bound `MAX_AGE`

`MAX_AGE` is 14 days, fixed in v1 (open decision 8), in milliseconds as `slotTime` is. An update,
an anchor or a replayed step is refused when `effNow − slotTime(store.finalized.slot) >
MAX_AGE`. Past it, the store's committee may be one whose members have exited, and nothing the
wallet holds can tell a real later chain from one that committee signed afterwards. 14 days is
the age helios checks at bootstrap (`networks.rs:125`), here checked on every update. Without
finality, new anchors stop once the chain's period reaches the finalized header's period + 2
([Processing an update](#processing-an-update)), and a non-finality longer than `MAX_AGE`
stops the light client: no forced update moves the finalized header. The servers' window (129
periods before Gloas, 56 under it) never binds first.

**Offline**, counted from the configured checkpoint or the last refresh: up to `MAX_AGE`, the
next start catches up by period updates, at most 14, verified in order; longer, the overview
says in red "Light client checkpoint too old (<date>): a new one is asked at the next start, or
now in lkd settings → Light client", and `--propose` runs at the next start.

### The evidence file

`<home>/lc/<chain>.evidence`, nothing secret. `lkd-lc` opens it before its sandbox with
`O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC`, mode `0600`, under an exclusive `flock`. It sets
`RLIMIT_FSIZE` to 2.25 MiB and ignores `SIGXFSZ`, so an overrun returns `EFBIG` instead of
killing it.

| Offset | Size | Content |
|---|---|---|
| 0 | 4 KiB | Header: magic, version, chain, genesis validators root |
| 4 KiB | 64 KiB | Conflict block: magic, sequence, length, SHA-256, then both updates. Written only on a halt; survives checkpoint changes; cleared only by `lkd-lc`, at its next start after `lkd settings` writes `lc_clear_conflict = <sequence>` |
| 68 KiB | 1 MiB | Copy A: magic ‖ sequence ‖ length ‖ SHA-256 ‖ payload |
| 68 KiB + 1 MiB | 1 MiB | Copy B, the same |

The payload: the checkpoint, its bootstrap, the newest one or two grid bootstraps, the best
update of each period, the grid updates, the latest finality update, and the finalized
checkpoints and committee roots kept for `MAX_AGE`; sized for 14 periods, at most about 960 KB.
As built in LC5 ([as built](#the-store-and-the-evidence-as-built-lc5)): the checkpoint, its
bootstrap, the update that set each next committee and the latest accepted update; the
checkpoints and committee roots are rebuilt from those at `Load`, not persisted. Since the refresh
([Refresh](#refresh), payload version 2): also the newest grid checkpoint whose bootstrap
verified, its root, the update that proved it and that bootstrap (one grid checkpoint, not two;
the grid update is kept beside the replayed updates, not among them): at most about 52 KB more
on mainnet (a bootstrap and a full update), so a payload of 32 committee-setting updates, the
latest, the bootstrap and the grid checkpoint is about 0.97 MB by the containers' sizes
(estimate, not measured), within the 1 MiB copy; 14 days need about 13.
A write goes to the inactive copy with `pwrite64` then `fdatasync`: no rename, no truncation.
**The shell's part** (`crates/lc/src/evidence.rs`, LC1): a new, empty file gets its header
(magic `LKDLCEV1`, version 1, the chain id, a zero genesis validators root while no light client
runs); a header that is not this version's for this chain, a link at the path (`O_NOFOLLOW`) or a
file another `lkd-lc` holds is refused, said on standard error, the file left as it is, and
`lkd-lc` runs without evidence. The conflict block and both copies are handed to `Load` as their
regions hold them, as far as the file reaches; framing, sequence and checksum inside a region are
the core's. `Persist(copy, payload)` writes the payload at the start of its copy's region; a
payload larger than the region (1 MiB, below `Load`'s 16 MiB cap) is refused before anything is
written.
`Load` takes the newest copy whose payload holds the configured checkpoint's bootstrap and
verifies from it, step by step at `Tick`, with `effNow = max(now, newest verified attested
slot)` and `MAX_AGE` at every step, to be proved as `Refinement.LedgerFile.pick_highest_code`
is: a torn or forged copy falls back to the other; when neither verifies, `lkd-lc` fetches the
checkpoint's bootstrap, and when no source serves it the overview says "Light client: no source
serves the checkpoint's bootstrap" and values stay yellow. **The evidence carries no trust**:
what loads is what a run of verified updates from the configured checkpoint, within `MAX_AGE`,
gives. It keeps a start fast and independent of sources still serving an old bootstrap.

## The clock (G6)

```text
effNow        = max(clock, slotTime(newest attested slot of an update verified by two thirds))
clock behind ↔ slotOf(clock) < newest attested slot of an update verified by two thirds
```

- **Only verified data moves `effNow`**, and only the attested slot, which the signature
  covers (it is in `hash_tree_root(attested.beacon)`); `signature_slot` is not signed. Under
  H_slot an honest supermajority signs a block's root only once its slot has come, so real time
  is at least `slotTime(attested slot)`.
- A source's unverified claim of a newer slot only triggers a fetch ([Catch-up](#catch-up)); a
  claim it cannot back marks it faulty for the round. One source cannot stall the wallet with
  claims.
- Hints only make the wallet more cautious: more hints never make it accept an update it would
  otherwise refuse (25i).
- **Clock behind** is said in red on the overview and in Settings, with the gap. `lkd-lc`
  answers `Account` `NotAnchored` meanwhile (LC6, the decision of 2026-10-26), so values fall back
  to one endpoint's path, yellow, though age is judged against `effNow`.
- **Clock ahead** makes the store look old; past `MAX_AGE` it stops and asks for a new
  checkpoint. When every source's claimed head lies far behind the clock (unverified, used for
  wording only), the message adds "or your clock is ahead".
- `slotTime` and `slotOf` follow the chain's slot schedule (milliseconds, from `Forks`), are
  total, and use checked subtraction. No clock floor is persisted (N9).
- **Residual**: a clock set back, two thirds of the keys of the store's old committee, and netd
  or every source together defeat `MAX_AGE`. Whether tor's consensus time could bound the clock
  is not established.

## UI

### The overview

Each line names its anchor, in the terminal and the window alike, which share the App; the
labels keep the overview's 14 columns (`tui.rs:4054-4088`), and `Chain` keeps its meaning:

```text
Balance       1.2345 ETH (proved at block 21,734,112, 14 s ago)
Nonce         12 proved at block 21,734,112; 12 next on the node; keyd last signed 11
Light client  2 sources, 498/512 signed, final to 21,734,050, checkpoint 9 d old
```

On one endpoint's path (LC2, as built; a quorum's until 2026-10-28) the first two lines are
already these, without the age: "Balance       1.2345 ETH (proved at block 21,734,112, on
rpc1.test's word)", with a yellow warning naming the endpoint ("Your balances rest on
rpc1.test's word until the light client anchors them: …"), or "(the node's word: <why>)" in
yellow, and "Nonce         12 proved at block 21,734,112; 12 next on the node; keyd last signed
11".

On Sepolia under Gloas the block is the parent payload's, one or more slots behind the head.
`Spec.OverviewText` takes the signers and the finalized block for the Light client line. When
`lkd-lc` cannot anchor, the line says why and which fallback holds, on own-node routes as "(proved
at block N of your node)":

```text
Balance       1.2345 ETH (proved at block 21,734,112, on rpc1.test's word, not anchored: light client catching up)
```

**As built (LC6, `lc6/ui`).** An anchored balance reads "1.2345 ETH (proved at block N,
signed by 498 of 512 of the sync committee; final up to F)", green while the anchor is younger
than `F` (two epochs: 12.8 minutes on mainnet and Sepolia, 16 s on a development chain under the
minimal preset, `lkd_ui::light::fresh_ms`) and the cross-check agrees; ", 3 h ago" past `F`,
"; your node disagrees at block N (not final)" or "; not cross-checked with the node" in
yellow. The Light client line and the failure states below are `lkd_ui::light::overview_lines`,
under the balance in the terminal and among Home's alerts in the window (green lines are not
alerts). The foreign-nonce alarm is red for an anchored nonce of a single-key keystore account
(not a hardware wallet's, nor one derived from recovery words: `Info.path` empty), worded
"Nonces 14 to 15 were consumed by transactions or authorizations lkd did not sign (…). Someone
else holds this key."; yellow, as LC2 built it, otherwise. Speed-up and cancel are offered under
`reads::may_replace` with `fresh` the anchor's freshness.

**LC1's differential** (`crates/ui/src/lc.rs`, `compare`; `tui.rs`, `App::ask_lc`): `lkd-lc` is
not yet authoritative, and the overview's lines are today's. Each time the overview's refresh
proves the selected account itself (netd's `ProvedAccount`, `check_proved`; since LC2
`ProvedAccounts`, checked by `check_head` then `check_account`), a thread of its own
asks `lkd-lc` for the same account (`Lc::account_within`, at most `ANSWER_WITHIN`, 62 s), so
that neither the UI's loop nor its worker waits on it, one ask at a time. The same block hash
with the same nonce, balance and code hash (which the wallet's EIP-7702 alert reads) changes
nothing on screen, and
neither does no comparable answer: `lkd-lc` down, stopped or busy, `Pending` to the end, an error,
or the account proved at another block. Another nonce, balance or code hash at the same block, or
an answer the client's re-check refuses, is a red line under the balance, in the terminal and the
window alike (a `Danger` alert, once, on Home above the total, whose note says what the address
in use was proved at), until `lkd-lc` agrees again; the value shown stays the wallet's own:

```text
Balance       10000 ETH (proved at block 1 of your node)
lkd-lc disagrees with the wallet's own check: its proof proves no account under that block's state
```

**As built (LC7, lc7-tokens-ui).** Under the Light client lines, a token line for each pinned
token the address in use holds once a token batch younger than an epoch proved it (D2), labelled
as an anchored balance is ("Token         25 USDC (proved at block N, signed by 498 of 512 of the
sync committee; final up to F)", green once its pin matched, its block cross-checked and its
anchor fresh; "; not cross-checked with the node" or ", 3 h ago" in yellow; "; frozen: the
token's blacklist flag is set" for USDC's bit 255, D17), or red when its pin did not match
("balance unproved: USDC's contract was upgraded after this release (…): its balance is unproved
until lkd is updated; the node's word shown"). Tokens lists every pinned token with how each is
known, "(the node's word: <why>)" in yellow where no proof younger than an epoch exists (D23);
the window's Home says the same of the address in use under its assets; `lkd balance` asks the
batch, then labels each token line. At start, the last session's token values come from the
newest snapshot (D22), "Cached        0x… 25 USDC (proved at block N, 3 min ago; from your last
session, checking)", until `CheckSnapshot` and the refresh replace them.

### The review screen

The review shows the proved balance and nonce with their block, signers and age, and says what
is not proved. A contract the transaction touches whose pin does not match, or is not proved, is
named with the reason and the code hashes known; for a deposit or a relayed withdrawal that
blocks the review (open decision 3).

**As built (LC7, lc7-tokens-ui; D1).** A review of a flow that sends funds to pinned contracts
(`pins::needs`: a deposit, its pool and what it uses, Privacy Pools' Entrypoint too; a relayed
withdrawal; ragequit; a stealth send, Multicall3 and the announcer; a registration, the registry;
a token send, the token's pin) has a `Contracts` block under the signed fields, in the terminal,
the window and on the command line: "Contracts     code pinned, proved at block N: Tornado's 1 ETH
pool and the 2 contracts it uses" (green; N the block the flow's own needs were proved at, or
"blocks A to B" when they straddle anchors, never the batch's newest block for a contract proved
at another: the second review's finding, 2026-10-28; Settings' Pins row likewise names the matched
pins' blocks, the batch's when none matched); else one line per contract ("<name>: pin unproved:
<reason>", "<name>: its code is not the code this release reviewed (block N)", "<name>: upgraded
after this release (implementation 0x…, seen at block N)", "<name>: not pinned in this release");
"Contracts     code not checked: no light client" where none is configured; "Contracts
checking code at block N…" while the review's own batch, asked when it opened, is out. A blocked
review adds "Blocked       <reason>: nothing can be signed" (and, for a Privacy Pools relayed
withdrawal, that ragequit gives the deposit back whatever the Entrypoint runs) and offers no
answer: `y` and `W` take nothing, the window's Sign and send is off, the command line refuses
(exit 2). One the outcome could block offers none while checking either. An acknowledgment is
`W` in the terminal, Sign and send anyway in the window, `anyway` typed on the command line,
which `--yes` never gives, as it never answers `keyd`'s warnings.

### Never-stuck screens

The unsettled-nonce line, resume, speed-up and cancel ([`03-wallet-ui.md`](03-wallet-ui.md))
take three states: the pending nonce says whether the node holds the transaction, the proved
nonce whether it is mined.

```text
Nonce 12: signed, but the node does not have it (node's next 12): resume (a), cancel (x)
Nonce 12: waiting, not mined at block 21,734,112 (proved nonce 12): speed up (u), cancel (x), or wait
Nonce 12: settled at block 21,734,140 (proved nonce 13); inclusion not proved yet
Nonce 12: mined in block 21,734,131 at index 57, succeeded (proved)
```

The first is 03's line, unchanged. Speed-up and cancel are offered only under `may_replace`
(G11). As built (LC2), the second and third lines are under the transaction's hash, at the
head the last refresh proved, in the terminal and the window alike; the fourth is LC8's.
As built (LC8, `lc8/ui`): once the transaction is mined, the fourth line is under its receipt
when the light client proved its inclusion (`proved::included_line`), green, with "(proved, not
final)" until the proving header is final and "(proved under an earlier checkpoint)" for a record
kept under a checkpoint since moved; until then the line under the receipt says the inclusion's
state ("Inclusion     mined in block N (the node's word); seen, not yet proved"), yellow, or red
for a refusal. A transaction settled by nonce for good (D7) reads "settled by nonce at finalized
block N, inclusion unproved" in the history. As built (LC9, lc9-history; D40): the settled line
is final once the account at the finalized block F settles the nonce too
(`proved::final_account`): "Nonce 12: settled at block 21,734,160, final (proved nonce 13);
inclusion not proved yet" on the transaction's screen and in the window, "settled by nonce at
block F, final (proved nonce p), inclusion unproved" in the history and `lkd history`; until
then the head's line, with "; not final: your node refuses proofs at block F (…)" when your own
node refuses the proof at F (D42), or the disagreement when F's cross-check finds another block.
Speed-up and cancel follow the head's proof, never F's. On the command line, `lkd speed-up` and `lkd cancel` refuse, before `keyd` is asked, when
the proved nonce, within `F`, is past the last nonce `keyd` signed: the case `03-wallet-ui.md`
lists as deferred, where the node refused the replacement and a replacement was used up;
without a proved nonce they behave as today. 03's unsettled-nonce paragraph is updated to match.

### The foreign-nonce alarm

```text
Nonces 14 to 15 were consumed by transactions or authorizations lkd did not sign (proved nonce 16, keyd's last 13)
```

Red for a keystore account at an anchored nonce; yellow, worded "not signed by lkd", for
hardware-wallet and seed accounts (open decision 17) and on one endpoint's path. After a restore
with an empty ledger it does not apply. As built (LC2, one endpoint's path), yellow under the
overview's nonce line and among Home's alerts:

```text
The node reports nonces lkd did not sign: nonces 14 to 15 were consumed by transactions or authorizations keyd did not sign (proved nonce 16 at block 21,734,112, keyd's last 13). Another wallet holding this key sent them, or the endpoints that proved it are wrong.
```

### Settings: the Light client group

Since 2026-10-28 the group starts with **the toggle** (On/Off, `L`; `light_client = off` or on
again, [`03-wallet-ui.md`](03-wallet-ui.md#light-client-toggle)) and, when `lkd` asks about a
first checkpoint, its question (the root, what each source said, Take this checkpoint `A`, Not
now `N`; Ask the sources again `G`); "Checkpoint from" says `unanimous:<n>` as "all n beacon
sources named it, taken without a question (on their word: trust on first use)". The rest:
Settings shows what `lkd-lc` reports; only `lkd settings`, on a terminal, changes the sources and
the trust root. The
group's meaning line: "Beacon endpoints see over Tor that an lkd light client is online and
when; never your addresses."

- **Checkpoint**: the root in groups of four, its slot, epoch, date and age, where it came from
  (`typed`, `agreed:k/n`, `refreshed`), and how to check it elsewhere.
- **Sync**: the finalized slot and epoch, the anchor's slot, block and signers, whether the next
  committee is known, the last update and its source, `MAX_AGE`, the next fork `Forks` knows and
  its date, or "no fork known beyond <fork>" (G8), and "Your clock: on time" or "Your clock: 3 h
  behind the chain".
- **Sources**: each beacon source, its route, its last answer or error, faults and why;
  one-source mode.
- **Beacon data** (decision 28): "through Tor", or "directly — faster; reveals that this IP runs a
  light client and when, nothing about your addresses", on the Privacy page beside the opt-ins
  (`lkd_ui::settings::BEACON_TOR`, `BEACON_DIRECT`), with public beacon sources only. The window
  changes it in its Privacy form, as the other privacy settings, through `lkd`'s control socket;
  `lkd settings` (Light client) too, saying what it reveals when it is turned on; `lkd doctor` says
  the route and whether this kernel holds `lkd-beacon` to ports 443 and 80. On the direct route the
  Light client group's sources read "…, TLS, directly" and "…, plain HTTP, directly", and its
  meaning line "Beacon endpoints see from this IP that an lkd light client runs here and when".
- **Execution proofs**: the head cross-check of the last anchored block, and while a refusal
  stands, "your node refuses proofs at block N" (LC9, D42: the anchor's refusal first, until a
  read of that kind is answered again; no per-endpoint record).
- **Pins** (LC7): how many of the chain's pinned contracts the last pin batch proved as pinned,
  at which block and how long ago, and those that are not, by name and why; "checking code at
  block N…" while a batch is out; "code not checked: no light client". The Networks page showing
  it asks a batch at most once an epoch (D21).
- **Evidence**: the periods held, the next refresh, "refresh needed".
- **Public caches** (G19, D34; LC7, lc7-pools-ui): what this session read of the chain's
  caches (how many regions of how many, items and size, the blocks they are final up to), how
  they are checked (against the mark this wallet keeps in `keyd`'s journal, trees against the
  roots the light client proved), and what the syncs found to say (two fetches disagreeing, a
  region discarded); before any sync, "N kept by lkd-lc in the wallet's home, not read yet this
  session". The group's notes say what they show at rest: "The public caches are plain files in
  lkd-lc's directory, lc/<chain id>.cache in the wallet's home. They name no address, but anyone
  who reads this disk sees which pools this wallet synced, and up to which block. Rescan rebuilds
  them from each pool's deployment." **Rescan from deployment**, a safe edit (it weakens nothing
  and costs the fetches): `R` on the Networks page in the terminal, the "Rescan public caches"
  button in the window; `lkd-lc` empties every region of the chain in its file, then `keyd`
  keeps a mark of nothing for each.
- **Halt**: the conflict's two updates (slots, roots, signers), how to check them, or the
  record kept as history.
- **Sandbox**: `lkd-lc`'s report, as `keyd`'s.

**As built (LC6, `lc6/ui`).** `lkd_ui::light::group`, one of `Settings::groups`, on the Networks
page of the terminal and the window alike: Checkpoint (grouped by four), Checkpoint from (slot,
epoch, date, age, where it came from), Sync (the phase, the last anchor's slot, block, signers,
finalized block and age, the clock), Sources (one-source mode said), Execution proofs (the
cross-check), Evidence, Halt (when halted), and the meaning line. `lkd-lc`'s Status carries only
its phase, so the next committee, the last update's source and the next fork are not shown yet,
nor the sandbox report.

`lkd settings` gains a Light client entry: refresh along the evidence now (`--check`); propose
a new checkpoint (`--propose`); type a root; the beacon sources (your beacon node, a public
list, root-only sources, each host checked as public endpoints are); clear the conflict record,
after showing it (`lc_clear_conflict`). A network change drops `checkpoint`, `checkpoint_from`
and the beacon lists, which belong to one chain, and the change's review says so.

### Failure states

Principle 6: say what is happening. Sending stays possible in every state (open decision 16):
`keyd` checks nothing it reads, and a stalled light client must not hold funds hostage; the
review says what is and is not proved. Only deposits into, and relayed withdrawals through, an
unchecked pool block (open decision 3).

| State | The overview says (as built: `lkd_ui::light::overview_lines`, the terminal and the window) | Values |
|---|---|---|
| Checking evidence | "Light client: checking its saved evidence" (yellow) | Yellow, today's check |
| Syncing | "Light client catching up: values are checked as before meanwhile" (yellow); the planned "2 days behind" is not built | Yellow, today's check |
| No checkpoint | "Light client off: no checkpoint set (Settings → Networks)" (yellow); with one set and `lkd-lc` running none, "Light client off: lkd-lc runs none on this chain" | Yellow, today's check |
| Checkpoint being chosen (2026-10-28) | "Light client: choosing its checkpoint, asking the beacon sources; values are checked as before meanwhile" (yellow) | Yellow, today's check |
| Checkpoint asked (2026-10-28) | "Light client: a checkpoint to confirm, which the beacon sources did not all name or which follows a halt; Settings → Networks asks you" (yellow), then the phase's line when a checkpoint is set | Yellow, today's check |
| Not now, or none proposed (2026-10-28) | "Light client off for now: Settings → Networks turns it on, or the next start"; "Light client off: no checkpoint could be proposed; Settings → Networks asks the sources again" (yellow) | Yellow, today's check |
| Synced | "Light client  n sources, s/512 signed, final to F, checkpoint d old" (green) | Green |
| One source | "Light client from 1 beacon source, no cross-check" (yellow line); "from 1 of 2 beacon sources: <host> not answering since 14:02" is not built | Green |
| No finality, frozen, or stalled | "No light-client update for <age>: sources not answering, or the chain not finalizing; values turn yellow" (yellow), once the last anchor is older than `F`; separate "no finality since <date>" and participation lines are not built | Green within `F`, then yellow, the age shown |
| Refresh needed | "Refresh needed: restart within N days, or a new checkpoint will be needed", from day 7 of the checkpoint's age, red from day 10, not for a refreshed checkpoint | Unchanged |
| Too old | "Light client checkpoint too old (<date>): a new one is asked at the next start, or now in lkd settings → Light client" (red); "check your clock" when every source is as far behind is not built | Yellow, today's check |
| Halted | "Two signed updates disagree on a finalized block: the light client stopped, evidence kept; a new checkpoint is asked at the next start" (red) | Yellow, today's check |
| Unknown fork | "The chain moved to a fork this wallet does not know: update lkd" (red), only when every source that answers, at least two, says so | Yellow, today's check |
| Clock behind | "Your clock is behind the chain" (red), beside the anchoring line | Yellow, today's check (`NotAnchored`, LC6) |
| Not running | "Light client stopped: lkd starts it again; values are checked as before" (yellow); "keeps stopping" after three restarts is not built | Yellow, today's check |
| No bootstrap | Not built as a line of its own: `lkd-lc` stays in its checking or syncing phase | Yellow, today's check |
| Proofs refused | "Your node refuses proofs at block N (reth: --rpc.eth-proof-window; geth keeps the last 128 blocks' state)": N F for a final read, the anchor otherwise, "at the light client's block" when `Head` names none (D42, built in LC9: `lc::window_words`); Settings' Execution proofs row says it | Yellow, today's check; unproved for D1 |
| Verifier disagreement | "lkd-lc and this wallet disagree on block N: values there are not proved" (red) | Unproved, yellow |
| Your node disagrees | "…; your node disagrees at block N (not final)" on the value's label | Yellow |
| Pin mismatch | In a review: "USDC: its code is not the code this release reviewed (block N)" (red) | The token's balance unproved |
| Pin upgraded | "USDC's contract was upgraded after this release (implementation 0x…, seen at block N): its balance is unproved until lkd is updated" (red for the privacy contracts) | The same |
| Pin unproved | "The code of Tornado's 1 ETH pool could not be checked at block N: <reason>" | Deposits and Privacy Pools relayed withdrawals blocked; a Tornado relayed withdrawal, ragequit, a stealth send, a token send and a registration ask an acknowledgment naming it (D1) |
| Pin stale (D58, LC9) | In the review: "Tornado's 1 ETH pool: pin unproved: proved at block N, 14 min ago: not proved now" | As pin unproved; the review asks its batch again once the anchor moves past N |
| Light client not answering (D60, LC9) | For a command typed without `lkd`'s settings, netd running beacon sources and `lkd-lc` missing or silent: "pin unproved: light client not answering"; a name or a price so typed is read on one endpoint's path with "(not proved at the anchor: light client not answering)" and a send to the name asks `W` (D46) | As pin unproved |
| Block replaced (D39, LC9) | "Block N was replaced (reorg, not final): values proved there withdrawn; proving again at block M" (yellow), until a batch proves values at M or past it | What a pin batch or pool sync proved at N withdrawn (pins unproved, a review's batch asked again; pools the node's word until proved again); a token's or a name's withdrawn by the free check, a review's name blocked until looked up again |
| No light client | No line: the overview says nothing of a light client none configured; Settings' group says "off: no beacon source configured (lkd settings → Light client)". The planned causes "your beacon node is not reachable over IPC" and "none on the development chain" are not built | As today |

## Invariants

A new group, 25, in [`INVARIANTS.md`](INVARIANTS.md); plus 10i, 26a and 26b, and restatements
of 19a, 19b, 14b and the journal codec row. Each theorem is listed in
[`proofs/Audit.lean`](../proofs/Audit.lean) in the milestone that ships it; a clause marked
(script), (review) or (tested) is not a theorem. The a37cf09 numbers 25a to 25f and 25h keep
their subjects, extended; its 25g (anchored reads) is now 25j, 25k and 25p, and 25g names
conflicts. LC7 and LC8 add 25t to 25w and restate 25k, 25l, 25o, 25q, 25r, 25s, 26a and the
journal codec row. LC9 adds 25x and 25y, and restates 10i, 15j, 25o, 25p, 25q, 25r, 25s, 25t's
and 25u's UI clauses, 25w and the journal rows; 26b gains its rule 5 (the readable Keccak-256),
and 28h and 29g are new in the ENS and prices groups. `INVARIANTS.md` holds each row in full,
this table summarizes.

| # | Invariant | Code | Lands |
|---|---|---|---|
| 25a | SSZ: each typed decoder equals ssz-specs' `deserialize` at its `Desc`, so decoding is total and canonical for the light-client containers of Electra, Fulu and Gloas (offsets start at the fixed part's end, increase, end at the buffer's end); the type decoded is the one `Forks` gives for the attested slot, which the source's tag must name; each SSZ-native `/updates` chunk's length is 4 plus its SSZ's, its digest the BPO-aware one; (script, review: the runtime rules, 26b) | `LkdLc.Ssz.{Decode, Containers, Frame}`, `ForkTable.digest` | LC3: decoded values fit, framing (proved); decoders against `deserialize`, digests (tested) |
| 25b | Merkleization equals ssz-specs' `hashTreeRoot` for those containers (none is a `ProgressiveContainer`: Gloas's progressive types enter only through the gindices); a normalized branch is binding: two different leaves accepted at one gindex under one root give a SHA-256 collision the specification computes (`Spec.Ssz.collision`, from `verifyMerkleProof_binding`), no axiom; the gindex table equals `getGeneralizedIndex` over transcribed `Desc`s; `LkdBase.Sha256.hash` equals `Spec.Sha256.sha256` | `LkdBase.Sha256`, `LkdLc.Ssz.{Merkle, Containers}` | LC3 (proved) |
| 25c | BLS12-381: `Fp` is `ZMod p`; `Fp2` to `Fp12` are fields, by the tower's formulas; the curve formulas are the ported `G1Group`'s; decompression and KeyValidate accept exactly the canonical encodings of points on the curve with `[r]P = O`, not the identity, and likewise the signature; `hash_to_G2` equals EthLib's rewritten `hashToG2` (RFC 9380, Ethereum's DST); `fastAggregateVerify` is true exactly when EthLib's rewritten `ethFastAggregateVerify` is, given H_vec's Miller-loop and final-exponentiation equation (except where `hash_to_G2(msg)` is the identity and the signature the identity's encoding: EthLib skips both pairs and accepts, the runtime refuses the identity signature; found in LC4b, so the equality needs `H(m) ≠ O`; and, LC4b's rest, where the signature is the identity's encoding EthLib accepts exactly when e(Σpk, H(m)) = 1, which non-degeneracy excludes for H(m) in G2); the cube lemma; (script, review: the runtime rules). Bilinearity and the maps' mathematics are not proved (N7). LC4b proved part of it, which `spec/INVARIANTS.md` 25c states; the rest is vectors only | `LkdLc.Bls.*` | LC4b, in part |
| 25d | Chain identity and domains: `computeDomain` and the signing root are the specification's; the fork version is the pinned table's at `max(signature_slot, 1) − 1`; genesis validators roots are distinct across the table's chains; `validate` is invariant in `signature_slot` within one period and one fork version, and such a change moves only `isBetter`'s last tiebreak; bytes tagged with another fork than `Forks` gives for the attested slot are refused | `LkdLc.{Forks, Store}` | LC5 |
| 25e | Bootstrap binds the checkpoint: a store starts only from a bootstrap whose header is valid at its slot's fork, whose header root is the configured checkpoint, whose committee is proved at its fork's gindex, and whose 512 keys pass KeyValidate; a refreshed checkpoint starts so from the bootstrap the evidence kept for it, offline; the root `lkd` writes reads back as itself; (tested) it is the one the one-shot's pipe carried and the launcher printed | `Store.bootstrap`, `Evidence.candidate`; `lkd_verified::config` | LC5 (config: LC6; refreshed start: LC6's refresh) |
| 25f | Acceptance: `process` is the specification's without the forced update or the optimistic header; every header the store keeps, anchors on or answers from passed `isValidHeader` at its own slot's fork; the finalized header moves only forward, to one proved by a finality branch in an attested header that two thirds (`3·popcount ≥ 2·size`) of the store's committee for that period signed; a committee enters only through a branch that verified, and an all-zero branch carries the empty committee; no period is skipped; updates below two thirds are refused; `isBetter` is a strict preference; the anchor is the newest attested header two thirds signed, the first verified winning at one slot | `Store.{validate, process, isBetter, anchor}` | LC5 |
| 25g | Conflicts: two finalized checkpoints of one epoch with different roots, or two committees for one period, each side verified and signed by two thirds, halt the store; comparison covers every update whose signature verifies under a committee held for its period, against the checkpoints and committee roots kept within `MAX_AGE`, before the relevance check, and a mismatch is a conflict only after BLS; a halted store accepts nothing and answers nothing as proved until a new checkpoint; the pair is persisted before any other effect; `Load` halts on a stored pair only when both verify from the configured checkpoint and disagree; any two sets of at least 342 of 512 overlap in at least 172 | `Store.conflict`, `Lc.step` | LC5 |
| 25h | The age bound: every update accepted, every anchor answered and every replayed step has `effNow − slotTime(finalized slot) ≤ MAX_AGE`, so the evidence carries no trust beyond `MAX_AGE` from the configured checkpoint; the root `--check` prints is the finalized header of an update a store reached from the configured checkpoint proves as a grid checkpoint, within `MAX_AGE`, its kept bootstrap verifying for it (the launcher's write: 25e) | `Store.fresh`, `Evidence.{onGrid, provesGrid, checkGrid}`, `Lc.reached` | LC5 (the refresh: LC6) |
| 25i | The clock: `effNow` (ms) is the clock or the newest verified attested slot's time, whichever is later; no unverified claim enters it; more hints never make an update acceptable; "clock behind" exactly when the clock's slot is before the newest verified attested slot; `slotTime` and `slotOf` are `compute_time_at_slot_ms` and `compute_slot_at_time_ms` over the schedule, total, with checked subtraction | `Store.effNow`, `Forks.{slotTime, slotOf}` | LC5 |
| 25j | EL binding: an anchored EL header is the one whose Keccak is its hash, tagged by its beacon header's own slot (`Parent` exactly when its epoch is at or past `GLOAS_FORK_EPOCH`), for the anchor and for the finalized header behind `AccountFinal` and the finalized EL number. `Own`, an `electra` header: `execMatches`, `timestamp = slotTime(slot)/1000`, `parentBeaconBlockRoot = parent_root`. `Own`, an upgraded header: the timestamp and `parentBeaconBlockRoot`. `Parent`: by its own EL fork, `slotNumber < slot` and `timestamp = slotTime(slotNumber)/1000`, or a pre-Amsterdam timestamp before the Gloas fork's, equal to `slotTime(k)/1000` for some `k < slot` | `LkdLc.Anchor` | LC6 |
| 25k | Facts: a fact at (N, hash) was read by `El.Mpt` from a proof under the state root of the header bound by 25j; a storage fact is that account and, under its storage root, each slot's value, zero for a slot proved absent (`Facts.storage`), at the keys `Pins` derives (a token balance's `keccak(pad(owner) ‖ pad(q))`, the pools' keys, EIP-2935's `N mod 8191`); a pin's storage conditions hold under the same root; "final" only for a fact proved at the finalized EL block; the values an endpoint sends beside its proof are never answered. One table, `LkdLc.Pins` (D16): its derived slots' widths from one lemma, its literal fields by `decide`, and `lkd_verified::pins` refined against it row by row (`Refinement.Pins`), not generated; (tested) the keys and the table's data against the chain, at one block per chain whose hash two providers gave (`lkd-lc-pins-test`) | `LkdLc.{Facts, Pins}`; `lkd_verified::pins` | LC6 (storage facts and the table: LC7) |
| 25l | Inclusion: a `proved j ok fin` verdict on `(h, N, i)` under an anchor `A` implies `N`'s hash `hN` is `A`'s own (`N = A`) or, with `A − 8191 ≤ N < A`, what the EIP-2935 history contract (its account holding the EIP's code) holds at slot `N mod 8191` under `A`'s state root by `Spec.Mpt`; `keccak(header) = hN`, the header is a known fork's canonical field list with `number = N` (14b); the transactions and receipts are canonical lists of nonempty envelopes, as many of each; `keccak(tx_j) = h`; tx `j` and receipt `j` are item `j` under the header's `transactionsRoot` and `receiptsRoot`, each the Yellow Paper's TRIE (`Spec.Mpt.Trie.root`) of its list's ordered map, read there by `Spec.Mpt.lookup` from the model's proof and by any other proof only short of a Keccak collision; tx `j` is a known type's envelope and receipt `j` one of the same type whose status is `ok`; `fin` is `A`'s finality. `ahead`, `tooOld` and `tooLarge` exactly as their conditions. Restated in LC8's phase 2 for D36's order (`Inclusion.settle`: the body's shape, both roots, then the hash looked up), so `notInBlock`, `transaction` and `receipt` mean the proved block says so (`verdict_notInBlock`, `verdict_transaction`, `verdict_receipt`), and a result settled once is the verdict under any anchor proving the same hash (`verdict_eq_settle`) | `LkdLc.El.{Trie, Typed, History}`, `LkdLc.Inclusion` | LC8 (the core; phase 2: D36's order) |
| 25u | The composed theorem, `lkd-lc`'s half, for G12 (D27): an `Included` answer proved (0) replies at once to an `Included(h, N, i)` query and names the configured chain; its proving header is the anchor's attested header, two thirds of the committee signed (not final), or the store's finalized header (final), its EL header the one `Anchor.bind` keeps for it (25j); the block hash is what EIP-2935's proof at that header gives for `N` (or its own hash), and `Inclusion.verdict` there is `proved` with the answer's index, status and finality (25l). No run invariant: the job keeps each result with the witness that it is `settle`'s (`PlanIncl.Settled.sound`). The UI's half (its re-check, the head cross-check, D3's persistence) is tested | `LkdLc.{Included, PlanIncl}` | LC8 phase 2 (`Lc.Included.included_sound`) |
| 25x | `Head` and `BlockHash` (LC9, D38, D41): a `Head(final)` answer is the anchored or the finalized EL header with its anchor; a `BlockHash(n, final)` answer at P proved means `n`'s hash is P's own or what EIP-2935's slot holds under P's state root, read by key set 6 at P's EL hash, on `Shared` (10i), routed by P's hash (tested); the UI's reorg check and withdrawal (D39, tested) | `LkdLc.Blocks`; netd `lc_storage::endpoint_key`; `lkd_ui::reorg` | LC9 (`Lc.Blocks.head_sound`, `blockHash_sound`, `blockHash_status`) |
| 25y | The UI's halves (D49 to D51): what the refined re-checks accept, given what the UI asked, H_lc-free (`Spec.LcCheck.*_accepts`), stating every value shown, gated on or kept; composed with `lkd-lc`'s halves under H_lc for balance and nonce (final included), tokens, pins, pools, inclusion, `Head`, `BlockHash`, the snapshot records the UI writes, D7's outcome 1 and the gate's pass (`LkdProofs.Lc.Ui`); not names and prices (`Ui.name_sound`, `Ui.prices_sound` not built) | `lkd_verified::{lc_check, pin_gate, inclusion_keep}`; `Spec.LcCheck`; `Refinement.LcCheck` | LC9 (`Ui.account_sound` and its siblings) |
| 25m | Nonces: `settled n ↔ p > n`; `may_replace` only while `p ≤ n`; the alarm exactly when `last = some m ∧ p > m + 1`; under H_nonce, `p ≤ n` means no transaction at `n` is included up to that block, `p > n` means `n` was consumed, and the alarm means values above `m` were consumed by transactions or authorizations `keyd` did not sign | `lkd_verified::reads::{settled, may_replace, foreign_nonce}` | LC2 |
| 25n | Evidence: `Load` takes the newest copy whose payload holds the configured checkpoint's bootstrap, or keeps it as its grid checkpoint, and verifies from it, else the other, else none, a bounded amount a step (the grid checkpoint a step of its own); `Persist` writes only the inactive copy; only `PersistConflict` writes, and only `ClearConflict` clears, the conflict block; a store loaded from any bytes is one a run of verified updates from the configured checkpoint, within `MAX_AGE`, gives | `LkdLc.Evidence` | LC5 |
| 25o | lcproto: every frame has one encoding, decoding is total and canonical, frames fit 64 KiB, queries are typed, and every answer names its chain id, genesis validators root and checkpoint; the Lean and the Rust codecs are one specification | `LkdLc.Wire`; `lkd_verified::lc_wire` | LC1; LC6's frames (`CheckSnapshot`, the anchored `Account`, `Snapshot`) in LC6-0; LC7's and LC8's (the cache frames, `MakeTokenSnapshot`, `Token`, `Pin`, `Pool`, `Included`, `TokenRecord`, error 8 `NotPinned`) restated; LC9's (`BlockHash` and `Head`, queries `0x0f` and `0x10`, answers `0x8e` and `0x8f`, error 9 `NodeWindow`) restated |
| 25p | The composed theorems (below): `lkd-lc`'s half for balance and nonce, final answers included since LC9 (`anchored_sound` with the hypothesis that the answer is not final, `anchoredFinal_sound`); the UI's half at the value level, `Ui.balance_line_sound` restated as `Ui.account_sound` (D49) | `Lc.anchored_sound`, `Lc.anchoredFinal_sound`, `Ui.account_sound`, and their siblings | LC6 (balance, nonce), LC7 and LC8 (`lkd-lc`'s halves of the rest: 25t, 25u), LC9 (final answers; the UI's halves, 25y) |
| 25q | The lc channel: request and reply datagrams have one layout each, decoding is total and canonical, a datagram is at most 60 KiB, and the requests are exactly 10i's typed requests; netd answers a non-canonical datagram `Failed`, changing nothing (tested); netd's rounds, `Started` and the shell's two-phase deadlines (tested, D43) | `LkdLc.Wire.Channel`; `lkd_verified::lc_channel`, netd | LC1; LC6's requests, codes and responses in LC6-0; LC7's and LC8's (`ElBlock`, `ElReceipts`, `ElStorage` with its key sets, `StorageProof`, `BlockBody`) restated; LC9's (`Started`, code 12 `Window`) restated |
| 25v | The public caches (G19, D8, D9): `lkd_verified::cache`'s regions, each item's and each slot's one encoding, `choose` and `tree_extends` (proved, refined); `lkd-lc`'s store, one file per chain with two slots per region, appending only at the staged end or at 0 and syncing the items before their slot; its shell answering the cache frames itself, a closed connection's staging dropped; the UI using a region only once its items carry the digest of the newest `CacheMark` (journal kind 10) this wallet wrote, a tree or the association set only once it extends to the root G16 proved (so a cached tree differs from the chain's only by a hash collision, H_tree), a set's closed cell only after two fetches returned the same items, and committing only final items (tested). What remains (N1): a log every fetch missed; a compromised UI's set items with a matching mark, until a rescan | `lkd_verified::cache`; `lkd_lc::{cache, shell}`; `lkd_ui::{cache, pool_proofs}` | LC7 (the formats proved; the store, the shell's and the UI's clauses tested) |
| 25w | The pins' gates (G14, D1): every review of a flow that sends funds to pinned contracts names each contract it needs (`pins::needs`) with its state and offers what D1's table gives (`pins::act`): blocked, no answer at all; an acknowledgment, `W` (`anyway` typed, never `--yes`); or passed. A contract counts as pinned only when `lkd-lc`'s answer checks again in the UI and the head cross-check of its block agrees; while the review's own batch is out, a flow it could block offers no answer; with no light client configured nothing blocks, and the review says so (tested; the mixing review). Restated in LC9: the kernel proved (`lkd_verified::pin_gate`: each flow's needs, D1's table, freshness, D58, and the configured input, D60), the glue tested | `lkd_ui::{pins, token_proofs}`; `lkd_verified::pin_gate`; the terminal UI, the window, the command line | LC7; LC9 (the kernel, `Spec.PinGate`) |
| 25r | `lkd-lc`'s core, LC1: every query is answered at once, by the query's step (restated in LC9 for `AccountFinal`, `Head` and `BlockHash`, `Lc.Routed`, and the deadlines' clause, tested); an `Account` answer is proved by a `ProvedAccount` response the run received before, by the one-endpoint check (the header's own hash `Header.keccakB`, `Header.verify`, `Mpt.account`; restated 2026-10-28, no quorum), names the configured chain and answers a query for its address (25p's one-endpoint instance); a `Fetch` is only `ProvedAccount` for such a query, under a fresh tag, one per address; the state stays bounded; every effect fits its layout and every answer decodes; (tested) the same accept and refuse, and fields, as `check_proved`'s Rust | `LkdLc.{Lc, Ffi}`; `lkd_lc_core` | LC1; LC7: `step` in `LkdLc.Step`, `Token`, `Pin`, `Pool`, `Included` and `MakeTokenSnapshot` sent to their handlers under the fixed contract, the cache frames answered by the shell, never the core; LC9: `AccountFinal`, `Head` and `BlockHash` routed (`Lc.step_query`), the window failure ending a read at once |
| 25s | The verified cache (G19), your facts as snapshots: a snapshot's fact (an account's, or since LC7 a token's, fact type 2) is shown as proved at its block only when `lkd-lc` verified, from the configured checkpoint's evidence, the update that finalized the block, the EL header against it and the fact's proof; only facts at finalized blocks persist (script, review); nothing cached is shown as current (tested). The public caches' clause (a cached tree used only once it extends to the root proved at the anchor, H_tree) is 25v's since LC7 | The UI's snapshot writer and reader; `keyd`'s journal codec. As built (snapshots): `LkdLc.Wire.Snapshot`, `Lc.checkSnapshot`, `Lc.makeSnapshot`; `lkd_verified::snapshot`; `lkd_ui::snapshot`; `Lc.snapshot_held`; LC7's token facts (type 2: `Lc.tokenHeld`, `TokenHolds`) | LC6 (snapshots, built), LC7 (token facts; the public caches moved to 25v), LC9 (name facts, type 3, `Lc.nameHeld`; the records the UI writes, `lc_check::record_account` and `record_tokens`, 25y) |
| 25t | The composed theorems, `lkd-lc`'s halves, for tokens, pins, pools and token snapshots (D27): a `Token`, `Pin` or `Pool` answer replies at once to its query and names the configured chain; under the anchored EL header's state root (25j), `Spec.Mpt` reads from its certificate the contract's account and each slot's value at the keys `LkdLc.Pins` derives for the index asked (a token's balance, then its pin's slots; a pin's slots and, when its proxy holds the pinned implementation, that implementation's account; a pool's head words, then the root slot the first names), and its verdict is `Pins.verdict` over them; a `TokenRecord` holds only facts that hold at the finalized header, a token whose pin does not match left out; an index the chain's table lacks is `NotPinned` (8) | `LkdLc.{Storage, PlanStorage}`; netd's `lc_storage.rs` | LC7 (`Lc.token_sound`, `pin_sound`, `pool_sound`, `tokenRecord_sound`) |
| 10i | Egress v8, a restatement of invariant 10: 10a, 10d, 10e, 10f and 10g hold, plus the `Beacon` class's `GET`s, the `blocks/{slot}/root` path, `eth_getBlockByHash` and `eth_getBlockByNumber(N, false)` on `Head`, `eth_getProof` with typed keys at a block hash (implementations' and G9's `History(N)` on `Shared`, the latter moved from `Head` in LC9, D38), and G12's requests by hash in the transaction's group only, each in the group the table gives; `Light(src)` credentials injective; restated for plain HTTP to a public beacon source, and for the direct route (decision 28): a `Clearnet` or `ClearnetTls` stream only for a configured public beacon source whose route is `Direct`, to exactly its host on 443 or 80, never from `egress::stream` | `egress`, `isolation` | LC6 |
| 19a | netd's view, restated: as today, plus the datagram socket it inherits on its standard input, whose other end `lkd-lc` holds; tor's SOCKS directory when a beacon source needs it; over TCP, the beacon node's port beside the node's | `lkd-netd`'s `sandbox`, `crates/launch` | LC1, LC6 |
| 19b | The UI's view, restated: its `connect` reaches `keyd`'s, netd's and `lkd-lc`'s sockets and no other socket of the user's | `lkd-ui`'s `sandbox` | LC1 |
| 14b | Block headers, restated: `decode` also reads `transactionsRoot` (4), `receiptsRoot` (5), `parentBeaconBlockRoot` (19) and `slotNumber` (22) where the fork has them | `header::decode`, `LkdLc.El.Header` | LC1 |
| Journal | The journal codec row, restated for kind 7 (`Snapshot`, G19: restated in LC6, with `keyd`'s retention and rewrite; LC7's token facts) and kinds 9 (`Included`, 120 bytes, with its outcome and the checkpoint root; [Records](#records)) and 10 (`CacheMark`, 55 bytes: the chain, the cache, the count, the block and the items' digest), with `INVARIANTS.md`'s rows Journal `Included` records (the UI's clause: D3's and D7's rules) and Journal cache marks; kind 8 left to the approvals; `decode_remember` still refuses `Sent` | `lkd_verified::journal`; `keyd`'s `journal::superseded` | LC6 (kind 7), LC8 (kinds 9 and 10), with the storage review |
| 26a | `lkd-lc`'s sandbox ([Sandboxes](#sandboxes)); restated in LC7: one descriptor more, the public caches' file, opened before the sandbox when `lkd-lc` serves, and `RLIMIT_FSIZE` at 320 MiB | `crates/lc`'s `sandbox` | LC1, LC7; reviewed, tested |
| 26c | `lkd-beacon`'s sandbox ([Sandboxes](#sandboxes), decision 28): no file, IPv4 and IPv6 sockets only, TCP connects to 443 and 80 (Landlock ABI 4), nothing of the user's received | `lkd-netd`'s `direct::sandbox`, `bin/lkd-beacon` | LC6 (decision 28); reviewed, tested |
| 26b | Runtime separation: each runtime library's closure and FFI module are its `CheckCore` row's (`LkdCore`'s closure never holds `LkdLc`); every theorem in them rests on the axioms `AXIOMS.allow` lists; every aborting builtin's site is in `ABORTS.allow`; no module but `LkdBase.Keccak` runs the readable Keccak-256 (rule 5, LC9); `keyd` never depends on `lkd-lc-core` (reviewed: the planned `just rust` check is not built) | `scripts/CheckCore.lean`, `check-core.sh` | LC0, LC1, LC9 (rule 5); checked by scripts |

10i, 19a, 19b, 14b and the journal codec row are restatements of existing invariants, and each
needs a second reviewer, as 10a to 10f did; so do LC7's and LC8's restatements (25k, 25l with
D36's order, 25o, 25q, 25r and the moved step theorems, 25s; 26a, the sandbox's) and the new
statements of 25t to 25v, and LC9's ([Second reviewers (LC9)](#second-reviewers-lc9): 25o,
25q, 25r with `Routed` and `step_query`, 25p with `anchored_sound`'s hypothesis, 25s, 25t's and
25u's clauses, 25w, 15j, the journal rows, and the new 25x, 25y, 28h and 29g): `lean-gate` was
not run on them (the user's word, 2026-10-27).

### The composed theorems

From the bytes `lkd-lc` received to the line the UI shows, in two halves. The composition is
new: `check_proved` is reviewed code today, with no theorem of this shape.

```lean
-- lkd-lc's half, over LkdLc's definitions (the code that runs), about the run itself.
-- `us` pairs each update with the clock it was judged against; `received ins` is the set of
-- objects decoded from the Load and Fetched inputs.
theorem Lc.account_sound (cfg) (ins : List Input) (a) (ans)
    (h : answer (run cfg ins) (.account a) = .proved ans) :
  let st := (run cfg ins).store
  st.halted = none ∧
  ∃ boot s₀ (us : List (Time × Update)) L hdr acct,
    boot ∈ received ins ∧ (∀ tu ∈ us, tu.2 ∈ received ins) ∧ L ∈ us.map Prod.snd
    ∧ htr boot.header.beacon = cfg.checkpoint ∧ Store.bootstrap cfg boot = some s₀   -- 25e
    ∧ Store.run cfg s₀ us = st ∧ anchor st = some L                                 -- 25f, 25g
    ∧ ans.anchor = Anchor.summary cfg st L                                          -- 25o
    ∧ effNow st - slotTime cfg st.finalized.slot ≤ cfg.maxAge                       -- 25h, 25i
    ∧ 2 * cfg.committeeSize ≤ 3 * popcount L.bits
    ∧ Bls.fastAggregateVerify (participants (committeeFor st L) L.bits)
        (signingRoot (htr L.attested.beacon)
          (computeDomain domainSyncCommittee (forkAt cfg (L.sigSlot - 1)) cfg.gvr)) L.sig  -- 25c, 25d
    ∧ elBinding cfg L hdr                                                           -- 25j
    ∧ El.Header.verify ans.rlp L.elHash = some hdr                                  -- 14b
    ∧ El.Mpt.account hdr.stateRoot a ans.proof = some acct                          -- 14c, 14d
    ∧ ans.balance = acct.balance ∧ ans.nonce = acct.nonce

-- the UI's half, over the Aeneas-refined lc_wire, header, mpt and format_units
theorem Ui.balance_line_sound (cfg : UiConfig) (bytes) (a) (line)
    (h : Ui.balanceLine cfg a bytes = some line) :
  ∃ ans hdr acct, LcWire.encode ans = bytes ∧ ans.anchor.chain = cfg.chainId
    ∧ Header.verify ans.rlp ans.anchor.elHash = some hdr
    ∧ Mpt.account hdr.stateRoot a ans.proof = some acct
    ∧ line = Spec.OverviewText.balance (formatUnits acct.balance 18) hdr.number ans.anchor
```

`Anchor.summary` fixes the slot, the beacon root, `elHash = L.elHash`, `signers = popcount
L.bits`, the finalized EL number, the age, the final flag, and the chain, genesis validators
root and checkpoint; so the UI's `ans.anchor.elHash` is `lkd-lc`'s `L.elHash`. The halves are
linked by H_lc: the bytes the UI read on `lkd-lc.sock` in reply to its query `q` are
`LcWire.encode (answer (run cfg ins) q)`, for the inputs `lkd-lc` received and the `cfg` the
launcher gave it, and the UI's `cfg.chainId` is the one `keyd`'s `GetInfo` reports. The
committee size and `maxAge` come from the release's chain table (`LkdLc.Forks`), never from
configuration. The **binding** version adds a chain `honest` with `cfg.checkpoint` on it, and is
stated over signatures in `received ins`: the balance shown is the balance at a block that two
thirds of a committee of `honest` signed as head (final: a block `honest` finalized), or the
specification computes a SHA-256 collision, or a Keccak-256 collision, or those members signed
a block they did not hold as head (excluded by H_sc, H_bls and H_vec). The same skeleton covers
the nonce and "settled" (adding H_nonce), token balances (adding the pin and H_tok), pins, pool
roots (adding H_tree), and inclusion (adding the ordered-trie binding). `format_units` is
proved today; `Spec.OverviewText` is new, after 15d's review text.

Outside the theorems: the checkpoint (H_cp), committee honesty and BLS (H_sc, H_bls), the
chain's execution (H_exec), Lean's compiler and runtime and the shim (H_rt), the mathematics
the vectors check (H_vec), that the UI renders the line it computed (tested), the clock's
residual.

**As built (LC7, LC8).** `lkd-lc`'s halves are proved for every answer LC7 and LC8 add (D27), on
`anchored_sound`'s skeleton (`AnchorProved`: the phase anchored, the store one the configured
checkpoint reaches, the anchor two thirds of the committee signed): `Lc.token_sound`,
`Lc.pin_sound`, `Lc.pool_sound` and `Lc.tokenRecord_sound` (25t), and
`Lc.Included.included_sound` (25u), which carries the job's witness to 25l's verdict. The UI's
halves stay LC9's: its re-checks (`lc::recheck_storage`, `lc::recheck_included`,
`pins::check_pin`, `token_proofs::check_token`, `pool_proofs::check`), the head cross-check
(`proved::cross_check_block`), D1's gates (25w) and D3's and D7's persistence are tested, not
proved.

**As built (LC9, lc9-ui-a part 2).** The UI's halves are proved at the value level (D49), H_lc-free
(25y): the UI re-checks every answer with `lkd_verified::lc_check`, given what it asked, and
`Refinement.LcCheck` proves the Rust computes `Spec.LcCheck` on every input, whose acceptance
theorems (`account_accepts`, `accountFinal_accepts`, `accountEndpoint_accepts`, `pin_accepts`,
`token_accepts` with `token_balance_accepts`, `pool_accepts`, `blockHash_accepts`,
`included_accepts`, `head_accepts`, `recordAccount_accepts`, `recordTokens_accepts`) name the
inputs asked and every value shown, gated on or kept, in the terms `lkd-lc`'s halves use. So
`Ui.balance_line_sound` above becomes `Ui.account_sound`, a value, not a line (D49). The pairs
composed under H_lc (`LkdProofs.Lc.Ui`) are part 3's.

**As built (LC9, lc9-ui-a part 3).** The pairs are composed in `LkdProofs.Lc.Ui`. H_lc is each
theorem's hypothesis `h`: the answer the UI decoded is one a step of a run of `lkd-lc` from the
configuration `cfg` the launcher gave it sent to the UI's connection `c`. No theorem assumes the
UI's chain or checkpoint are `lkd-lc`'s: each concludes that the chain the UI asked is the
configured one and the UI's checkpoint, when it has one, the one the run starts from
(`Configured`), that the answer replied to the UI's query (`Replies`), and the header the UI read
is the EL header `Anchor.bind` keeps (`bind_verify`: the same bytes under the anchor's EL hash).
`Ui.blockHash_sound` does so given its caller's checks of the identity, the anchor and the
answer's block and final flag as hypotheses (`reorg::judge`'s glue, tested), which
`history_hash` does not take.
`Ui.balance_line_sound`, at the value level (D49), is:

```lean
theorem Ui.account_sound (h : .answer c (.anchored id x a) ∈ (step (run cfg ins) i).2)
    (hui : Spec.LcCheck.account chain cp address false id x a = some r) :
    Configured cfg chain cp ∧ Replies i c (.account address) ∧
      ∃ l st L hdr, AnchorProved cfg (run cfg ins) l st L ∧
        Anchor.bind l.chain L.header a.header = some hdr ∧
        r = ⟨hdr.number, L.header.elHash.data.toList, hdr.timestamp, hdr.stateRoot, a.account⟩ ∧
        Spec.Mpt.account hdr.stateRoot address a.proof.data.toList = some r.account ∧
        x.slot = L.header.beacon.slot ∧ x.beaconRoot = L.header.root.data.toList ∧
        x.isFinal = false
```

| The UI's theorem | composes `Spec.LcCheck`'s | with `lkd-lc`'s half | What the UI shows, gates on or keeps is |
|---|---|---|---|
| `Ui.account_sound` | `account_accepts` | `Lc.anchored_sound` (kind 2) | the account at the anchor's EL header |
| `Ui.accountFinal_sound` | `account_accepts` | `Lc.anchoredFinal_sound` | the account at the finalized header's |
| `Ui.accountEndpoint_sound` | `accountEndpoint_accepts` | `Lc.account_sound` (LC1's kind 1, 25r) | the account a `ProvedAccount` response the run received proves |
| `Ui.token_sound` | `token_accepts` | `Lc.token_sound` | the balance word and the verdict at the anchor's EL header (a proxy's implementation code not read: H_6780) |
| `Ui.pin_sound` | `pin_accepts` | `Lc.pin_sound` | the verdict, the implementation and its code, there |
| `Ui.pool_sound` | `pool_accepts` | `Lc.pool_sound` | what the pool's words say, there |
| `Ui.included_sound` | `included_accepts` | `Lc.Included.included_sound` | a proved verdict under P, the anchor's or the finalized header as its final flag says, N's hash re-checked, the tries `lkd-lc`'s |
| `Ui.head_sound` | `head_accepts` | `Lc.Blocks.head_sound` | P's EL header |
| `Ui.blockHash_sound` | `blockHash_accepts` | `Lc.Blocks.blockHash_sound` | block n's hash under P's EL header |
| `Ui.record_sound` | `recordAccount_accepts` | `Lc.record_sound` | the record `lkd-lc` made for the address asked, at the finalized header of a store `Reaches` gives (the records the UI writes merge such records' facts under the same header bytes, `snapshot::split`, with D47's name records beside them: glue, tested) |
| `Ui.tokenRecord_sound` | `recordTokens_accepts` | `Lc.tokenRecord_sound` | the token record, there, each token fact held |
| `Ui.settled_sound` | `Ui.accountFinal_sound` | `Spec.InclusionKeep.settledKeep_iff` | D7's outcome 1 only when the account at F has a nonce past the transaction's |
| `Ui.gate_pass_sound` | `Ui.pin_sound` | `Spec.PinGate` (`combine_pass_iff`, `cause_matched`, `settle_matched`, `light_up`) | a passing review: each need pinned, its answer's index the need's, matched, cross-checked agreeing and fresh, the chain the configured one (`Configured`), the contract's code the pinned one at an `AnchorProved` block at most `gate_bound_s` before the UI's clock |

Each docstring names the glue it rests on, tested: which re-check each screen calls and with what
it asked, the flow's target (the transaction's `to`), the configured input and the socket's state
(D60), the verdict's mapping onto the gate's `Found` (`foundOf`), and D7's inputs from the
journal and the head cross-check. Not built: `Ui.name_sound` and `Ui.prices_sound`.

### Tested, not proved

That the honest chain's data is accepted (completeness: the sync vectors and live runs);
bilinearity and the maps (vectors); netd's beacon client, its JSON re-encoding, its paging and
its channel decoder (25q); that netd hands over every source's answer; the planner's liveness,
order and backoff; the file I/O around the evidence; the sandboxes; the runtime rules beyond
`CheckCore` (recursion depth, the builtin-abort sites: review and fuzzing); that the launcher
writes the root it printed; that `balanceOf` is the decoded value (H_tok); the pin table's data
and the pools' key layouts, checked at one recorded block per chain whose hash two providers
gave (`lkd-lc-pins-test`; the Rust table is refined against the Lean one, D16); the public
caches' store, the shell's cache frames and the UI's checks of the caches (25v); netd's storage
reads, block bodies, re-encoded envelopes and held pages; the progress of the planner's storage
reads and of G12's job (`lkd-lc-plan-test`, `lkd-lc-incl-test`, e2e).

**Since LC9, proved and no longer here** (25y, 25w, the Journal `Included` row): the UI's
re-checks at the value level, given what it asked (`lc_check`, composed with `lkd-lc`'s halves
under H_lc in `LkdProofs.Lc.Ui`); D1's kernel with each flow's needs and its configured input
(`pin_gate`); D3's and D7's keep rules, outcome 1 from `AccountFinal` (`inclusion_keep`); the
head cross-check's verdict (`pin_gate::crossed`); D58's freshness (`lc_check::fresh`).

**LC9's, tested, not proved**: the rendered lines (D49's line level, `Spec.OverviewText`, is not
built) and which re-check each screen calls with what it asked; netd's rounds, `Started`, the
shell's two-phase deadlines and its queued-in-netd rule (25q's tested clause), and their 90 s
precondition (e2e `lc-deadlines`); D42's matching of the nodes' error messages; D44's netd reads
at a block the UI names, and their routing by address; the name-fact writer and its order
against `keyd`'s retention (D47), and D48's rule for which names persist; G9's withdrawal (D39)
wherever a value is held, a review's name included; D45's wait and D46's acknowledgment, and
the configured rule names and prices share with the gate; the gate's glue (the flow's target is
the transaction's `to`; the configured input from `lkd`'s settings or netd's `Health.beacon`, and
the socket's state, D60); `included::next`'s reopen rule and `history::Book::status`; G11's
`AccountFinal` cadence and its call sites (`proved::final_account`); `Lc::head` asked once per
anchor to name D42's block; H_clock under D58, a clock set back that `lkd-lc` does not see as
behind; the UI's words.

### Other documents in the same changes

Each done, as built (2026-10-27):

- `INVARIANTS.md`: the group above, in order, with its introduction for each milestone; the
  "Verified reads" note "Not yet wired into netd or the UI" brought up to date; the
  guarded-signing rows 19a to 19f renumbered 27a to 27f, since 19a and 19b already name the
  sandboxes (LC0, `build/lc0`, `f52bd93`), and master's 19c and 19h taken in as 27c and 27h at
  LC9's merge; 26b; 28h and 29g (LC9's names and prices); the Keccak-256 row names
  `LkdBase/KeccakFast.lean`, run by `keyd` and `lkd-lc`. **Done.**
- `AGENTS.md`, Runtime Lean: the rules name every runtime library and its FFI module,
  `LkdLcDev`'s development export included, the rule that every `Nat.powMod` modulus is a
  nonzero literal, and the fast Keccak-256's import rule (rule 5); the ABI paragraph names
  `crates/lean-rt` and `crates/lc-core`; fast versions proved equal in `LkdProofs` described as
  the practice (open decision 6, D54). Rust lints: `crates/lean-rt/src/runtime.rs`,
  `crates/core/src/abi.rs`, `crates/lc-core/src/abi.rs` (the sandbox's calls in
  `crates/sandbox/src/sys.rs`, open decision 14), `crates/netd/src/sys.rs`, and the test-only
  `crates/ui/tests/sandbox.rs`. Proofs: the kernel replay and the `debug.` ban. Secrets: every
  class egress allows, each over Tor or to your own node, the direct route the one exception;
  the second-review classes (D57). **Done.**
- `00-plan.md`: decision 5's third amendment, the process table (`lkd-lc`, `lkd-beacon`), the
  trust base. **Done.**
- `04-verified-reads.md`: its opening; its "What remains trusted" names the light client.
  **Done.**
- `03-wallet-ui.md`: the labels, the overview, the unsettled-nonce paragraph, `lkd status`, the
  Settings sentence. **Done.**
- `06-tor.md`: the isolation table, and "A block with its transactions … is never asked of a
  third party", which G12 relaxes (open decision 23, D4's fallback and D59 accepted); the one
  class that may leave without tor, the public beacon sources on the direct route (decision
  28). **Done.**
- `08-accounts-journal.md`: the `Included` record and the `Snapshot` row's token and name facts.
  `13-tokens.md`: Multicall3 replaced. `15-desktop-window.md`: the window's labels.
  `17-ens.md` and `18-prices.md`: the reads at the anchor (D44 to D48). `crates/ui/src/settings.rs`:
  its notes (Where the wallet reads, worded per configuration, D42). **Done.**
- `proofs/core/lakefile.lean`: each library's docstring as built (`LkdBase` with the fast
  Keccak-256, `LkdLc`'s five exports, `LkdLcDev`'s one). **Done.**

## Tooling

**State as built (LC9, 2026-10-27).** LC0's tooling is in the tree: `just proofs` runs
`check-kernel.sh` (631 modules at LC9's integration, 519 s with two jobs), `check-axioms.sh`
(5,012 theorems of `Audit.lean`) and `check-core.sh`, which audits each runtime library against
its row of `scripts/CheckCore.lean` and `proofs/ABORTS.allow` (27 builtin-abort sites at LC9);
its rule 5, no compiled code but `LkdBase.Keccak`'s calling the readable Keccak-256, came with
master's fast Keccak-256 at LC9's merge. `lean-gate` was not run on LC7, LC8 or LC9 (the
user's word, 2026-10-27): every restated statement is listed for the second reviewer instead
([Second reviewers (LC9)](#second-reviewers-lc9)). The parallel builds of LC7 to LC9 shared
machine-local lock scripts (`.tools/lc78-heavy.sh` and `lc78-e2e.sh`, two slots each;
`lc9-funs.sh`, one slot for a `Funs` build or a Kani run, taken before the heavy one), never
committed. The rest of this section is the state LC0 started from.

**State on 2026-10-25.** The Lean 4.35 bump is committed and builds clean: `afba3fb..d2c94fa`
on `build/lean-4.35` (Lean 4.35.0, Aeneas `74aabd5`, VCVio `88efe971`, Mathlib v4.35.0
`56a00585`). `build/turbo-lean` (`f340df6`) is `feat/gui-app` `77cb07b` plus the same six
commits rebased (`b771afa..7458b02`), plus turbo-lean and lean-native; it lands in LC0, before
any `LkdLc` code, and `build/lean-4.35` is not merged separately. Its `lean-gate` already bans
`debug.` options, requires every `@[csimp]` equation to be listed in `Audit.lean`, and leaves a
file holding one to `just proofs` instead of turbo-lean, which refuses `@[csimp]` outright: that
is the fix the user's decision 2 asked for, since `AGENTS.md` prescribes `@[csimp]` for fast
code. `just ci` runs `lean-gate` after `just proofs`.

**Committed on `build/lc0`** (`b544a67..f52bd93`, on `build/turbo-lean`, not merged):

- `scripts/check-kernel.sh` in `just proofs`: the toolchain's `leanchecker` replay
  (`replayFromImports`, copied unchanged into `scripts/CheckKernel.lean`) of every module of
  `LkdProofs`, of `proofs/core`'s libraries, and of Aeneas's library and VCVio's algorithms, one
  module per call: four processes, about 8 GB and four minutes on this machine, where
  `leanchecker LkdProofs` itself would hold some two hundred environments at once (about
  46 GB). A module's own declarations are replayed into an environment loaded from its imports'
  `.olean` files, so what is not replayed is trusted: Mathlib and Batteries rest on Mathlib's
  daily `leanchecker --fresh` (`.github/workflows/daily.yml:68-73`), which runs on its master and
  nightly, not at our pin; ssz-specs, vendored into `LkdProofs` (LC3), is replayed with it. The `False`
  probe made with `set_option debug.skipKernelTC` passes `check-axioms.sh` and fails the replay.
- The `debug.` ban in `just proofs` (the replay script refuses any `debug.` option first), and
  `lean-gate`'s ban and `@[csimp]` audit, all over the repository's tracked sources
  (`git ls-files`) and the extraction, never `.lake`, where a fresh clone holds after
  `just proofs` Mathlib's tests that set debug options and 16 dependency files declaring
  `@[csimp]`; for dependencies the replay is the check.
- `scripts/CheckCore.lean`, moved out of `proofs/core`, and `check-core.sh`: one row per runtime
  library, and every theorem of a runtime library checked against `AXIOMS.allow`, so a
  `@[csimp]` proved by `sorry` fails.
- Guarded signing's invariants renumbered 27a to 27f.

**Left for LC0**: `lean-gate` diffed against the merge-base, not the tip of `master` (about 500
commits behind `feat/gui-app`); the builtin-abort allowlist `CheckCore` reads (since built, in
LC4a: `proofs/ABORTS.allow`, [Runtime rules](#runtime-rules-and-how-they-are-audited)); D7
and D19; and the docs that call
lean-native turbo-lean's counterexample engine (`README.md`, `scripts/turbo-lean.sh:3`, the
`lean-fast-check` recipe), corrected: that engine is turbo-lean's own
(`gpu_fastcheck.rs:3838`), and `lean_native_certified` is a hard-coded self-test
(`CoreCLI.lean:959-962`).

**turbo-lean** (`d4c5da92`; its `Cargo.toml` says MIT, there is no LICENSE file) and
**lean-native** (`8de44e78`; no licence) are development tools only (the user's decision 2):
fetched and built outside the repository, never in a binary, never the authority on a proof.
`just lean-check` checks one declaration with turbo-lean: 1.1 s after an edit on our proofs,
against 52 s for `lake build`. Inside `lean-gate` it is also an extra gate of `just ci`, whose
failure blocks and whose pass counts for nothing. Its limits, measured: it accepted a proof of
`False` made with `debug.skipKernelTC`; "OK" for one declaration does not mean the file builds,
and a cache hit checks nothing; `pr-verify` passed a change that broke a dependent file; it
refuses any `@[csimp]`; its MCP tool fails open, and `audit-spec` and `agent-step` exit 0 on
failure; `just lean-fast-check` runs its counterexample search, which reads `Nat` as a wrapping
64-bit integer and reported counterexamples to three proved lemmas; it sends telemetry by
default, so `scripts/turbo-lean.sh` runs it with telemetry off, no daemon and no network. No
step of this plan uses lean-native. Measured on the BLS benchmark, it gives no speed-up (BLS
within ±3%, SHA-256 and SSZ 15 to 27% slower), its own executable crashes on this code, it
lowers `Nat` to a 64-bit integer while tagging the result `VerifiedKernelProof`, and it cannot
build a static library.

## Testing

**Vectors**, from consensus-specs **v1.7.0-beta.4** (`aa16bb4`; the standalone
consensus-spec-tests repository stopped at v1.6.0-beta.0), a committed subset, decompressed
from `*.ssz_snappy` by a test-only script (snappy never enters the wallet), hashed:

- **Minimal preset**, in `LkdLcDev` (built, LC5: `lake exe lkd-lc-store-test` in `proofs/tests`,
  run by `just lc`, over all of `proofs/tests/vectors/light_client`, 1.3 MB, hashed: the 15 `sync`
  cases and the three `update_ranking` sets of 57 pass, 121 checks, with `light_client_sync`'s
  steps 6 to 10 of each fork, from its first effective `force_update`, reported unsupported; and
  103 checks of lkd's own cases: an equivocation re-signed with the test keys halts the store and
  a `Load` again, one signature after bootstrap moves nothing, a skipped period, a synthetic
  chain over five periods and into a next-committee conflict, clock behind, too old, unknown
  forks, `Load`'s copies, a tampered one refused, the conflict block cleared): `light_client/sync` (Electra: `light_client_sync`,
  `light_client_sync_no_force_update`, `advance_finality_without_sync_committee`,
  `supply_sync_committee_from_past_update`, `gloas_store_with_legacy_data`; Fulu: the same plus
  `gloas_fork`; Gloas: the first four) and `update_ranking`. Their rules: `light_client_sync`
  runs up to its first effective `force_update` (`test_sync.py:225`), and a `force_update` in
  `*_no_force_update` is a no-op, its timeout not having elapsed; `finalized_header` is always
  compared, `optimistic_header` against the anchor or the finalized header, whichever is newer
  (every step has full participation); now is `slotTime(current_slot)`; each vector's fork
  epochs and `BLOB_SCHEDULE` build a test `Forks` table for the digests; `upgrade_store` upgrades
  the store to the Gloas form ([Objects](#objects)). The checks compare `slot`, `beacon_root` and
  `execution_root`.
- **Mainnet preset**: `single_merkle_proof` (the state's committees and finality root; the
  body's `execution_merkle_proof` for Capella to Fulu and `execution_block_hash_merkle_proof`
  for Gloas and Heze) and `ssz_static` for `LightClient{Bootstrap,FinalityUpdate,Header,
  OptimisticUpdate,Update}` of Electra, Fulu and Gloas, bytes and roots. Built in LC3: `lake exe
  lkd-ssz-test` in `proofs/tests`, over a committed, hashed subset in `proofs/tests/vectors/ssz`
  (42 `ssz_static` cases, the common containers' too, and the 12 light-client
  `single_merkle_proof` cases of Electra, Fulu and Gloas), with mutated offsets, sizes,
  `extra_data` and branches refused, the framing, facts.md's fork digests and SHA-256's NIST
  vectors: 444 checks. The `BeaconState` objects (about 3 MB each) are not committed, and no
  object's `hash_tree_root` is computed (`LkdLc.Ssz` has no `BeaconState` type), so a branch is
  checked under the root it climbs to, with its gindex and length against the pinned ones.
- **BLS** (LC4a, `lake exe lkd-bls-test` in `proofs/tests`, run by `just lc`):
  `general/altair/bls`, 12 `eth_fast_aggregate_verify` and 8 `eth_aggregate_pubkeys` cases,
  exactly the light client's operations; EthLib's BLS tests, the same 20 byte for byte;
  ethereum/bls12-381-tests v0.1.2's `fast_aggregate_verify` (12), `verify` (29),
  `deserialization_G1` (13) and `_G2` (15), `sign` (10) and `hash_to_G2` (4); RFC 9380's J.10.1
  vectors for `hash_to_G2` (with their DST), each of `u`, `Q0`, `Q1` and `P` compared; SHA-256's
  FIPS examples. Every one runs on the runtime layer and on EthLib's vendored readable layer,
  which `proofs/tests`, a Lake package requiring only `proofs/core`, compiles from `LkdProofs`'
  sources; the test also checks the hash-to-curve constants against RFC 9380 E.3's text and
  py_ecc's, runs the benchmark's self-tests, refuses one-bit mutations of valid signatures, keys
  and messages, compares the two layers off the vectors (hashing, `clear_cofactor` against
  EthLib's G.3, decompression, the final exponentiation's cube) and times an update and a
  committee (`--budget` fails above 20 ms an update). `scripts/bls-vectors.py` writes the
  vectors from the downloaded sources, each file's SHA-256 recorded.
- **Recorded fixtures**: a mainnet and a Sepolia (Gloas) bootstrap, a week of updates, EL
  headers (23-field Amsterdam on Sepolia) and proofs, token values against `eth_call`; Hoodi's
  configuration for the digest code.
- **Real blocks** (LC8, `lake exe lkd-lc-incl-test` in `proofs/tests`): mainnet block 26,270,755
  with an EIP-2935 proof at a later head and Sepolia block 11,985,890 (an Amsterdam header),
  `vectors/inclusion`, 1.4 MB gzipped, hashed, refetched by its `fetch.py`: every transaction
  proved and timed, both roots rebuilt to the headers', the other outcomes and a changed byte of
  each input refused ([as built](#inclusion-as-built-lc8-core)).

**Differential tests**: the compiled code against `lean --run` against `decide +kernel` on
small cases (the interpreter is about 300 times slower on scalar loops); the fast BLS layer
against EthLib's rewritten code; `LkdLc.El` against `lkd-verified`'s `header` and `mpt`; lcproto
and the channel in Lean against Rust; out of the tree only, py_ecc, blst (v0.3.17), helios,
etheorem's `EthCLLib` (domains, signing roots), jaune and evm-asm (tries, receipts).

**Fuzzing**: `step` through the FFI, for no abort and bounded time and memory; netd's channel
decoder.

**The fake beacon**: `lkd-e2e-beacon-gen` (built, LC6: `proofs/tests`, its command line in
`proofs/tests/README.md`), a pure Lean generator (a `lean_exe` outside the runtime libraries) that
a Rust HTTP server in `crates/e2e` runs over a JSON description of anvil's blocks and serves what
it writes, so no Lean networking; built by `just e2e`. `lake exe lkd-lc-plan-test` drives
`Lc.step` from its objects and recorded EL data to anchored answers (LC6, 58 checks), G19's
snapshots (33 more: `MakeSnapshot` at the finalized block, anvil's block 1 at an epoch's first slot;
`CheckSnapshot` held, a tampered fact and a tampered proof not held, another header, block, time
or tag not held, a bad signature, another chain or a byte past the record refused, too old under a
core bootstrapped two periods later, both queries unsupported without a light client; a snapshot
of period 3 against a refreshed start's store in period 2, `Pending`, then held once the store
reached period 3, a badly signed one `Pending`, then refused), and the refresh (22 more,
[Refresh](#refresh)). A committee
whose secret keys are `i + 1`, the minimal
preset with 1 s slots, a development fork table Electra → Fulu → Gloas, and state and body trees
built over anvil's real blocks in own-hash and parent-hash modes: beacon headers take
`parent_root` from anvil's `parentBeaconBlockRoot`, and slots map from anvil's timestamps against
a genesis given to anvil (`--timestamp`, and `--block-time 1` where blocks are mined on a timer;
chain 31339's anvil mines on demand). Served through the fake tor and the TLS proxy.

**As integrated (LC6, `lc6/integrate`).** The server is `crates/e2e/src/beacon.rs`: the five
beacon-API requests in SSZ from the generator's directory as it writes it (`bootstrap.ssz`,
`updates/<p>.chunk` in `/updates`' framing, `finality_update.ssz`, `optimistic_update.ssz`, block
roots in JSON from `roots`), plus `bootstraps/<root>.ssz`, the grid roots' bootstraps `--propose`
asks, added by the harness; the directory is swapped whole when the chain is generated again (the
line protocol LC6c's server first proposed was dropped: the generator writes a directory, and
every object served is its bytes). Faults for every source or for one host: silent, 500, a flipped
byte in every SSZ answer, the generator's `equivocation` as the finality update, a finality update
claiming a far-future attested slot. On loopback (your beacon node) or behind the fake tor and the
TLS proxy (`beacon1.test` to `beacon3.test`). Each scenario has an anvil of its own (chain 31337)
whose genesis is set minutes back (`--timestamp`), with a block mined every 4 slots since
(`evm_mine <time>`: every epoch and period starts with one, and each EL timestamp is its slot's,
as `Anchor.bind`'s `Own` check wants), and a mover that mines at the current second and generates
again every 3 s; `lkd start --dev-beacon` passes the generator's `dev` file on.

Scenarios (`crates/e2e/src/lc6.rs`), all run by `just e2e`: `lc-anchored-cli` and `lc-settings-cli`
(a stand-in `lkd-lc` on its socket; the configuration keys through `lkd doctor` and `lkd settings
--check`); and, following the fake beacon:

- `lc-own`: your beacon node on loopback: the balance anchored ("signed by 32 of 32 of the sync
  committee; final up to F") on the overview and in `lkd balance`, "Light client  1 source" and
  the one-source line, `lkd status` anchored, the bootstrap and finality updates asked.
- `lc-public`, `lc-one-source`: three, then one, public endpoints over the fake tor and TLS 1.3;
  every endpoint asked.
- `lc-direct` (decision 28): `beacon_route = direct`, your node on TCP, `beacon1.test` over TLS
  and `http://beacon2.test` in plain HTTP, both reached by `lkd-beacon` through `--dev-direct`'s
  map to the fake beacon on loopback (the TLS proxy for the first, its certificate checked against
  the test root): anchored from both, both hosts asked, no tor configured and no stream through
  one, `lkd-beacon` running under its filter with `no_new_privs` (`Seccomp: 2`, `NoNewPrivs: 1`),
  `lkd doctor` saying each source is reached directly and that beacon data goes directly.
- `lc-plain`: `beacon1.test` over TLS and `http://beacon2.test` in plain HTTP, both behind the
  fake tor: anchored from both, tor asked for the plain host on port 80 only with `Light(1)`'s
  credentials, `lkd doctor` saying which is plain; then the plain source alters every SSZ object
  (as an exit could): refused, the anchor kept from the TLS one.
- `lc-gap`: a checkpoint four sync periods old (as after the wallet was offline): caught up by
  period updates, anchored.
- `lc-low`: updates signed by 20 of the 32 members: nothing new anchored, "No light-client update
  for …", the balance's anchor shown with its age.
- `lc-stale`: a checkpoint near `LkdLcDev`'s `MAX_AGE` (ten minutes), the sources stalled since:
  "Light client checkpoint too old" (red); at the next start `--check` says `stale`, `--propose`
  asks both public endpoints for the grid root, which both name: written without a question
  (`unanimous:2`, since 2026-10-28), and the light client anchors from it.
- `lc-clock`: a second public endpoint claiming a far-future attested slot in every finality
  update: the anchor stays fresh from the first; then the chain mined three minutes ahead of the
  clock, committees and finality with it: "Your clock is behind the chain" (red), values on one
  endpoint's path.
- `lc-gloas`: anchored in own-hash mode, then one block past the Gloas fork (the epoch the
  description names): its beacon block names its parent payload, anvil's last block before the
  fork, a Prague header whose time is before the fork's, which `Anchor.parentOk` takes; `lkd-lc`
  answers that block anchored with `parent` set. What it does not cover, anvil having no Amsterdam
  headers: a parent with `slotNumber` (every Gloas block after the first), and a Gloas-form
  finalized header's EL lookup; both are `lkd-lc-plan-test`'s, on an Amsterdam header built over
  recorded fields.
- `lc-conflict`: the second public endpoint serving the generator's equivocation: the store halts,
  red; at the next start `--check` says `stale`, a checkpoint both sources name is proposed and,
  after a halt, asked about rather than taken (Settings → Networks; Not now), and the store halts
  again from the conflict block: still red.
- `lc-lying-el`: the node's proofs for the account altered by a proxy: "not anchored: the light
  client refused the proof".
- `lc-lying-netd`: every SSZ object altered on its way (the fake beacon flips a byte, which is
  what `lkd-lc` sees of a netd that alters them; netd has no altering switch): nothing new
  anchored, said.
- `lc-refresh`: the wallet, anchored from a typed checkpoint at a period start, runs until the
  chain passes the next period's first epoch: `lkd-lc` reaches that grid checkpoint and asks its
  bootstrap of the fake beacon, which serves every grid checkpoint's (`bootstraps/0x<root>`, the
  generator's). At the next start `--check` prints `checked`, `lkd` says "Light client checkpoint
  moved to slot S" and writes the root, its slot and `checkpoint_from = refreshed`, and `lkd-lc`
  checks its saved evidence and starts from the kept bootstrap (the fake beacon is not asked for
  it again), then anchors; `lkd settings --check` then verifies from the new checkpoint
  ([Refresh](#refresh)).
- `lc-cli`: `lkd settings --propose` against two public endpoints: both name the grid root,
  `checkpoint_from = unanimous:2` and `checkpoint_slot` written without a question, the wallet
  anchored from it.
- Since 2026-10-28 (`crates/e2e/src/lcdefault.rs`): `lc-agreed` (no checkpoint, two public
  sources naming the same grid root: written unasked, anchored; the light client's requests
  tagged `tor, verified` in Network activity and `lkd network traffic`), `lc-disagree` (the
  second source names another root, the fake beacon's `OtherRoot`: nothing written until
  Settings → Networks' Take this checkpoint, then `agreed:1/2`, anchored), `lc-default` (public
  endpoints with no light-client key and `--dev-suggested-beacon`: the suggested sources written
  and said once, the checkpoint taken unasked, anchored; Networks' toggle off behind the review,
  the indicator gone, on again at once).
- `lc-snapshot` (G19, on a seed keystore, whose journal is kept on disk): balances anchored, a
  snapshot written at the finalized block ("Snapshot saved: block N"); quit and start again: the
  snapshot's values shown at once, labelled "from your last session", before the fresh refresh's,
  then "confirmed by the light client", the refresh's value replacing the cached one; a tampered
  snapshot (the newest record again with a balance of 4242 ETH, kept by `keyd` through its socket
  as the UI keeps one): shown only as the last session's, checking, then "1 fact not held,
  dropped". The restart after the tampering may move the checkpoint to a grid checkpoint reached
  meanwhile ([Refresh](#refresh)); the snapshot is then `Pending` until the store catches up.

**End-to-end scenarios**: `lc-own`, `lc-public`, `lc-plain` (a source in plain HTTP),
`lc-direct` (the direct route),
`lc-one-source`, `lc-gap` (offline three
periods, caught up), `lc-low` (participation 300: nothing new anchored), `lc-stale` (past
`LkdLcDev`'s short bound: too old, then a new checkpoint), `lc-refresh`, `lc-clock` (an
unverified far-future claim does not stall; a clock behind is said), `lc-gloas`; `lc-conflict`
(red, and still red after a restart); `lc-lying-el`; `lc-lying-netd` (a `dev-insecure` netd
alters updates and proofs, and `lkd-lc` refuses them); `lc-tampered-answer` (a `dev-insecure`
`lkd-lc` alters a certificate, and the UI refuses it); `lc-mined` (anvil Prague),
`lc-nonce-alarm`; `lc-netd-restart`, `lc-killed` (the UI goes on, values turn yellow),
`lc-killed-mid-page` (`lkd-lc` stopped while its fetch waits on the node; netd still serves the
UI), `lc-killed-mid-body` (`lkd-lc` stopped while netd holds a G12 block of four pages and more
for it: `lkd balance` and `lkd status` answer within the UI's netd timeout, 40 s since D13's
numbers, and once continued the block is paged from netd's held copy, the node asked once),
`lc-netd-busy` (a broadcast and a receipt poll while G12's receipts are held 15 s at the node:
each answered after them, within the same 40 s), `lc-cli`; the sandbox soak.

**LC7's and LC8's tests** (built 2026-10-27; [As built](#as-built)). `lake exe lkd-lc-pins-test`
(`proofs/tests`, run by `just lc`): one recorded block per chain whose hash two providers gave
(`vectors/pins`: mainnet 26,280,412, Sepolia 12,012,139, recorded again 2026-10-28 for WETH's re-pin), every key the table derives as the
endpoint echoed it, every pin matched, every token balance `balanceOf`'s (USDC's frozen flag on
the blacklisted holder only), every pool root its contract's; the development chain's keys
against `cast`'s. `lkd-lc-plan-test` gains the plumbing test and LC7's cases (the fake beacon
over the recorded mainnet block: every pin, holder and pool, a lying or silent storage server,
`MakeTokenSnapshot` at the finalized header). `lkd-lc-incl-test` gains G12's job cases and times
the whole job, from the `Included` query to the proved answer, on the two kept blocks; with
`--budget` it fails above 1 s (`just lc` prints the times). `cargo test`: netd's `lc_storage`,
`lc_bodies`, `envelopes` (the kept blocks' JSON re-encoded to the vectors byte for byte) and its
held responses; `crates/lc`'s cache store, the shell's cache frames and both in the sandbox;
`lkd-ui`'s `pins`, `token_proofs`, `pool_proofs`, `cache` and `included`. The scenarios, on
chains following the fake beacon (`lc6::following`, with LC7's placements, `lc7::place_all`):
`lc-history`; `lc-tokens`, `lc-pins`, `lc-pools` (`lkd-lc`'s answers against `cast`, then a code
replaced, a condition failed, a proxy moved, a deposit moving a root); `lc-mined` (G12 in
`lkd-lc`); `lc-tokens-ui` (token lines proved; D1's gates in the terminal UI, the window and the
command line); `lc-pools-ui` (the reviews' proved roots) and `lc-cache` (the two-fetch rule, the
grid after a restart, a tampered item and a home with no mark each synced from deployment);
`lc-mined-ui` (G12's states, D3's and D7's records), `lc-netd-busy` and `lc-killed-mid-body`
(above).

**LC2's scenarios** (`crates/e2e/src/proved.rs`, in `just e2e`, on anvil, your own node):
`proved-balances` (a restored seed wallet's two addresses proved at one block of the node, as
`cast` reads them, in the overview, `lkd balance` and Home; its node behind a proxy that changes
one hex digit of address #1's account proof: #1 the node's word, yellow, with why, in all three,
#0 still proved; the proxy honest again, every balance proved), `foreign-nonce` (account 1 sends
once through `lkd`, then `cast send` from the same mnemonic path consumes the next nonce: the
yellow alarm on the overview and on Home, naming the nonce and `keyd`'s last), `settled-nonce`
(on an anvil that mines on demand, a transfer waiting at proved nonce 0 offers a speed-up and a
cancel; replaced outside `lkd` at its nonce and mined, it is "settled at block 2 (proved nonce
1); inclusion not proved yet", with neither offered and `u` doing nothing, and `lkd speed-up`
refuses before `keyd` prepares anything).

**LC1's scenarios** (`crates/e2e/src/lc.rs`, in `just e2e`), on anvil behind a proxy that can hold
`eth_getProof`: `lc-endpoint` (`lc-quorum` until 2026-10-28; `lkd` starts `lkd-lc`, which runs
sandboxed, as `/proc` shows, and proves the overview's account at the block the UI proved it at,
with the same balance; no red line; `lkd status` says phase endpoint), `lc-killed` (the UI goes on;
`lkd` starts it again at generation 2, which answers), `lc-killed-mid-page` (stopped while its
`ProvedAccount` fetch waits on the node: netd serves `lkd balance`, `lkd status` exits 1; continued,
it proves the account from the reply that waited in the channel, no second fetch), `lc-netd-restart`
(killed while its fetch waits on the node, its successor drops that reply and fetches for itself;
netd killed and started again by `lkd`, the channel serves `lkd-lc` again), `lc-tampered-answer`
(`lkd start --tamper-lc`: the red line, the wallet's own balance kept) and `lc-soak` (30 s, `just
e2e-lc-soak` ten minutes: the same process, still sandboxed, its resident size within 16 MiB of what
it was once warm). `lkd-settings` (settings changed from the UI through `lkd`'s control socket)
checks the launcher's side: netd started again on a new route leaves the same `lkd-lc` process
running, and a move to Sepolia starts it again at generation 2 on chain 11155111, ready before keyd
asks for the passphrase. On a fresh anvil (Foundry 1.5.1) at block 0 the account proof netd gathers
does not verify against the genesis header (the UI's own check refuses it), so the scenarios mine a
block first when none is.

**netd's side of LC6** (LC6a, `cargo test -p lkd-netd`): `tests/beacon.rs`, netd's own loop and
the channel against a fake beacon node and a fake JSON-RPC node on loopback: a finality update
and a bootstrap in SSZ forwarded with their fork's name, a JSON bootstrap re-encoded to the very
SSZ a Lodestar node served, a `gloas` JSON answer `NotSsz`, `/updates` in JSON (form `1`) and in
SSZ (form `0`, three pages pulled), a block's root, `404` as `NotFound`, a source slower than the
deadline `Unreachable` within it, a source not configured `Denied`, every request the fake saw
exactly the `GET`, `Host`, `User-Agent` and `Accept` egress v8 writes; `ElHeader` the RLP that hashes to the
hash asked (a block the node lacks `NotFound`), `ElProof` the endpoint's account fields and the
proof's nodes, accepted by `mpt::account` under that header's state root, both asked by
`blockHash`. `tests/sandbox.rs`'s `beacon-tcp` (your beacon node on loopback beside the node,
fetched in the sandbox, a third port refused) and `beacon-tor` (an onion beacon node through a
fake tor's SOCKS socket: one stream, kept, with the `light 000` credentials for that service and
port). Unit tests: `reencode` (the recorded fixtures byte for byte, versions and shapes refused),
`beacon::answer` (statuses, media types, fork names, roots), `upstream::endpoint_for` (decision
11), `reads::account_fields`, the arguments.

**Live** ([The live run (D52)](#the-live-run-d52), built by lc9-deadlines): `just e2e-lc-live`,
not in `ci`, builds the release binaries and the e2e debug ones, runs `./scripts/tor.sh`, refuses
a binary older than the newest commit of its sources (`crates`, `proofs/core`), naming it, and
runs `lkd-e2e --lc-live <tor> <release dir> <debug dir> <foundry> <root>`
(`crates/e2e/src/live.rs`): per chain of `LKD_LIVE_CHAINS` (mainnet and Sepolia), read-only over
Tor from a fresh wallet of anvil's words, the binaries keyd can run (stage 0), the survey,
`lkd init` and `lkd start` with the proposal's "<k> of <n> sources agree", the anchored label,
the lcproto answers re-checked as the UI does against the oracle's reads at the same block hash,
names and prices, and the request budget over one automatic refresh; each stage one deadline,
no retry loop, a failed stage probed at once; `e2e lc-live <chain>: green|inconclusive:
<why>|FAILED: <why>`, exit 0, 3 or 1. `lkd-e2e --lc-survey <tor>` is its stage 1 alone (no
wallet). `lc-live-dry` (in `just e2e`) runs the same step functions on the development chain:
three public sources over the fake tor and TLS, anvil the oracle, the survey's lines through
the wallet's fake tor, names and prices on `place_ens`'s and `place_prices`'s contracts, and the
probe of a source the scenario stops, whose 500 it meets again: inconclusive, naming it.
`lc-deadlines` (in `just e2e`) checks D43's deadlines under the wallet's own load ([As built,
lc9-deadlines](#lc9-deadlines)).

**LC9's tests** (built 2026-10-27; [As built (LC9)](#as-built-lc9)). `lkd-lc-plan-test` gains
`LkdTests.Lc9.History` (`AccountFinal`, `Head`, `BlockHash` and the window failure's ends) and
`LkdTests.Lc9.Deadlines` (D43's bounds and outcomes, never per-step fetch counts). `cargo test`:
`lkd-verified`'s `deadlines`, `lc_check`, `pin_gate` and `inclusion_keep`; netd's error mapping
on reth's, geth's and 4444 replies, kept sanitized, its rounds and `Started`; `crates/lc`'s two
phases and the queued-in-netd rule; `keyd`'s retention with name records; `lkd-ui`'s `reorg`,
`names` (the configured rule names and prices share with the gate, a replaced name in a
review), `snapshot` (the name facts' sizes beside a 27 KB update) and `pins` (D58, D60). Kani:
`lc_wire`'s and `lc_channel`'s LC9 frames at fixed lengths under a 16 GB cap. The scenarios, in
`just e2e`: `lc-proof-window` (D42: your node's refusals, reth's and geth's, named at the
anchor's block or F; public endpoints rotated); `lc-deadlines` and `lc-live-dry` (above);
`lc-final` (G11's settled line, final at F); `lc-reorg` (EIP-2935's slot for a shown batch's
block rewritten with another hash: withdrawn, proved again; the `History` reads on `Shared`, at
most `ASKS` a refresh, none at an anchor an `Account` read used) and `lc-fail-closed` (D60: a
deposit typed without `LKD_SETTINGS` while netd runs beacon sources and `lkd-lc` does not,
blocked); `lc-names-anchored` (D44 to D46) and `lc-name-facts` (D47, D48). `lkd-e2e
--lc-survey` and `just e2e-lc-live` once at the integration ([Milestones](#milestones)).

## LC7 and LC8: the design as decided

**Decided 2026-10-26, revised after two review rounds; built 2026-10-27** by thirteen tracks in two stages, integrated on `build/lc78-integrate`, the user's answers of 2026-10-27 in [The decision gate](#the-decision-gate). The user asked to start LC7 and LC8 with parallel agents, without looping verifications or the e2e suite. The tracks built from this section; the final integration folded it into the sections above ([What this section overrides](#what-this-section-overrides)), which, with the [As built](#as-built) subsections, say what was built. No track picked a tag, kind, row, name or index this section does not give, or edited another track's files ([Tracks and what they own](#tracks-and-what-they-own)).

### Scope

| Built | Not yet |
|---|---|
| G14 pins: code hashes, proxies and their implementations, storage conditions, linked libraries and verifiers; the review gates (D1) | `AccountFinal` and G9's reorg check by `History(n)`: LC9 (D25) |
| G15: the selected address's pinned tokens, with their pin's slots at the same anchor | ENS names as facts: type 3, query `0x0e` (D5; LC9: type 3 made by the UI, D47) |
| G16: Tornado roots and leaf counts, the PP pool's `currentRoot` and size, the association set's `latestRoot`, `assetConfig(ETH)` | ENS and price reads by storage proof: they kept the quorum head then (D32; LC9: read at the anchor, D44; one endpoint's head where the anchor fails, since 2026-10-28) |
| G19 public caches: trees, Tornado spent sets, PP deposits, withdrawals and ragequits, ASP leaves, stealth announcements | G13, G17, G18; the UI halves of the composed theorems (LC9) |
| Token facts in snapshots (type 2, `TokenRecord`) | Naming a transaction the wallet did not send (decision 22) |
| G12 phase 2: `Included` end to end, journal kind 9, the UI's states, `lkd status` | "Your node refuses proofs at block N" as a reason (LC9) |
| The head cross-check by header, as decision 18 says (D35) | |

### Decisions

The rows marked **the user's** are put to the user once, at the start of stage A ([The decision gate](#the-decision-gate)); meanwhile the tracks build the recommendation, each decision's code, unit tests and e2e steps in commits whose subject ends `(Dn)`, so that a no is a revert of those commits or the swap of the one constant named.

| # | Decision | Whose call |
|---|---|---|
| D1 (open decision 3) | **What a pin blocks, per flow, by who holds the funds.** Deposits (Tornado; Privacy Pools through the Entrypoint) and Privacy Pools withdrawals through `Entrypoint.relay` (lkd sets `processooor` to the Entrypoint, which receives the whole amount and pays recipient and fee through its implementation) are blocked on any cause: the code or the implementation's code not the pinned one, a proxy upgraded, a condition gating the flow failed, unproved, not pinned; a blocked PP withdrawal names ragequit as the exit. Tornado relayed withdrawals (immutable pools; the proof binds recipient, relayer and fee) are blocked on a code mismatch of the pool or of what it uses (verifier, hasher, library) or a failed condition gating them, and ask an acknowledgment naming the reason (W) when unproved or not pinned. Direct exits (ragequit, a direct Tornado withdrawal): W, never blocked. Stealth send: blocked on a Multicall3 code mismatch, W otherwise. Token send and registration: W, the token red. A condition carries `gates` (1 deposits, 2 relayed withdrawals, 4 direct exits, 8 sends): failed, it is a mismatch for the flows it gates and unproved for the others. Unproved: a light client configured in the settings (`light::configured`: a checkpoint and a beacon source) that is down, in phase 0, syncing, halted, too old, refused the batch, or has not answered the review's batch within `PIN_BATCH_WITHIN` (60 s); meanwhile the review says "checking code at block N…" and offers no confirm for a flow the outcome could block. None configured: nothing blocks, and the review says "code not checked: no light client". One table, flow × cause → block, W or pass (`lkd_ui::pins`); a no swaps in decision 3's table (every relayed withdrawal blocked on any cause, stealth sends W). **Costs**: a stalled light client, or your own reth node at its default proof window, blocks deposits and PP relayed withdrawals, never ragequit or a direct Tornado withdrawal; an Entrypoint upgrade blocks PP deposits and relayed withdrawals until a release pins the new implementation; a review opened while a block body downloads may wait up to a minute; blocking stealth sends on a Multicall3 mismatch departs from decision 16 | **The user's** (mixing review) |
| D2 (4) | Token proofs: the selected address, every pinned token in one batch (a batch never says which tokens it holds), on an explicit refresh and before a token send's review, at most once an epoch; the automatic refresh keeps `aggregate3`'s `balanceOf`, labelled the node's word, unless a proof younger than an epoch exists; another address once the user selects it. A no: on an explicit refresh only (one constant) | **The user's** |
| D3 (5, 19) | `Included`, journal kind 9, with the checkpoint root. Persisted: proved (0) only when final, after the UI's re-check of the certificate and the head cross-check of the proving header; too old (2) only when `keyd`'s `Sent.time` makes it plausible (sent more than 8191 slots and an hour before the anchor's slot time), else the node's hint is a lie, shown yellow and asked again; too large (3) only as `lkd-lc` answers it after `maxAttempts` attempts each said too large with N's header bound, and only with two or more public EL endpoints configured (attempts 0 and 1 then reach two of them) or your own node, else kept in memory and asked again next session; settled by nonce (1) per D7; refusals never (red, backoff). Ranking: a proved record is never superseded by 1, 2 or 3; a later proved record with another hN supersedes it. A refresh never reopens a record (a refreshed root is reached from the old one through the evidence, 25h): a record under another root than `lkd-lc`'s identity is shown "proved under an earlier checkpoint", and asked once more only when the current checkpoint came from a ceremony (`checkpoint_from` typed or agreed, as after a halt) and N is within 8191 blocks of the anchor. `Mined` stays the receipt's word. A no: decisions 5 and 19 as first recommended (every outcome recorded, the newest per hash winning; one constant). **Costs**: one record kind more; a refusal is asked again each session; with one public endpoint "too large" is never kept | **The user's** (storage review) |
| D4 (23) | G12's block and receipts from public endpoints: `eth_getBlockByHash(hN, true)`, its header-only form and `eth_getBlockReceipts(hN)`, by hash only, in the transaction's `Broadcast(n)`, from `el_endpoint(tx, attempt)`, with the EIP-2935 proof (`HistoryFor`) in the same group. Before D4's commit all three are own-node only; that commit allows them at a third party together, with `06-tor.md`'s exception. A no reverts it: on public routes the UI asks nothing and says "inclusion not checked on public endpoints (your choice)". **Cost**: 1.5 to 5.6 MB of JSON once per transaction on mainnet (PROBE measures it on the suggested endpoints, directly and over Tor); that circuit's endpoint, which knows the hash, learns the block. As built (the review, 2026-10-27): the endpoints that took the broadcast this session are asked first (`g12_endpoint`); past them, or in a later session, the endpoint the hash picks, on a circuit of its own, was not given the transaction and learns that a wallet asked for that block. **D4's fallback, accepted by the user on 2026-10-27:** after a restart, G12 reads go to `endpoint_for(tx)` when the broadcast's endpoints are unknown; that endpoint learns that some wallet cares about that block. The code also falls back within a session, past the endpoints that took the broadcast, which the user also accepted on 2026-10-27 (LC9's [D59](#decisions-lc9), yes: no change) | **The user's** |
| D5 (25) | Token balances (type 2) now; ENS facts (type 3, query `0x0e`) in a follow-up, `lc9/ens-facts`. A no starts it off the integrated tip. **LC9**: built in the UI instead (D47, D48, the user's yes, 2026-10-27): the selected account's primary name as type-3 facts the UI makes in each pass; query `0x0e` stays reserved | **The user's** |
| D6 (26) | A delta starts at the last committed block rounded down to a multiple of 50,000 (32 on the development chain, so e2e sees cells close), never before deployment; refetched logs deduplicated by leaf index or (block, log index). A no: another grid (one constant) | **The user's** |
| D7 (22) | Settled by nonce (1) only when the sender's nonce n is consumed at a finalized block (a `MakeSnapshot` record of the sender at the finalized header, re-checked, nonce > n; asked once when needed) and none of the wallet's own transactions at n has a receipt; terminal only while no receipt is known: a newer `Mined` record reopens G12 for that hash, and a proved record supersedes it. A no: shown from the anchored nonce (G11), never persisted | **The user's** (storage review) |
| D22 | `MakeTokenSnapshot(owner)`, answered `TokenRecord`, in the regular snapshot pass in place of `MakeSnapshot` for the selected address when a token proof was made since the last snapshot: one storage proof per pinned token at the finalized header, at most every 10 minutes, all on `Account(owner)`. A no reverts the UI's commits (lkd-lc's handler stays, unused) | **The user's** |
| D25, D32 | `History(n)` and `AccountFinal` in LC9, follow-up `lc9/history`; ENS and price reads on the quorum head, labelled k of n, follow-up `lc9/quorum-pins` (key-set tags 8 and 9 reserved). A no starts the follow-up off the integrated tip; the fast-forward does not wait for it. **LC9**: D25 built (lc9-history: `AccountFinal`, `Head`, `BlockHash` and key set 6, D38 to D41); D32's follow-up built in the UI instead of `lc9/quorum-pins` (D44 to D46, the user's yes, 2026-10-27): ENS and price reads at the anchor, `lkd-lc`'s `Head(false)` re-checked, netd's reads at its number and state root; key-set tags 8 and 9 stay reserved | **The user's** |
| D34 | Public caches at rest: plaintext in `lkd-lc`'s directory, they show anyone who reads the disk which pools were synced and to which block. Built: only what normal use synced (G19), said in Settings' Public caches row. Options: caches opt-in per chain; or every pool of a chain synced whenever one is (requests G19 says it never makes) | **The user's** |
| D8 | One file per chain, kept by `lkd-lc`'s shell, never in the Lean core. The UI checks each region against the newest `CacheMark` (kind 10) it wrote; trees and ASP leaves against their roots (G16, `tree_extends`); PP deposits by recomputing each commitment from value, label and precommitment and, with withdrawals' new commitments, against the PP tree's leaves (count equal). A set without a root (Tornado spent sets, PP ragequits, announcements) commits a closed grid cell only after two fetches of it returned the same items (two syncs, or twice in one run: netd's rotation sends the second to the next endpoint when two or more are configured); a mismatch commits neither and says so. Settings offers a rescan from deployment | Decided |
| D9 | `CacheRead`, `CacheAppend`, `CacheCommit` answered by the shell, whole items. A transfer belongs to the connection that staged it: the UI holds one connection (`lkd_ui::lc::CacheSession`) from its first `CacheAppend` to its `CacheCommit`, sent back to back at commit time; the shell drops a closed connection's uncommitted items (the staged end falls back to the committed count); another live connection's transfer is `Busy`. Offset: the staged end, or 0 to restart (both slots emptied and synced first); commit with count = staged. Every kind commits only items at or below the anchored answer's finalized EL number (G19: final only); trees and ASP leaves store the root the UI rebuilt there; at use, a failed `tree_extends` refetches the delta once from the next endpoint, then discards the cache and syncs from deployment. Commits at most every 10 minutes per cache and at exit, each followed by a `CacheMark` | Decided |
| D10 | Typed keys: channel kind `0x15` `ElStorage(attempt, hash, key set)`, key sets 1 to 7; `ElProof`'s keys byte stays 0; egress has its own `Keys`, mapped one to one by netd | Decided |
| D11 | `0x13` answers N's header first, then a flag: 0 the transactions follow, 1 too large. Past `MAX_BLOCK_BODY` netd asks `eth_getBlockByHash(hN, false)` on the same group and endpoint and answers the header with flag 1, so too large comes from `Inclusion.verdict` with body `none` and a header bound to hN; a `TooLarge` is asked again on the next endpoint up to `maxAttempts` | Decided |
| D12 | netd holds only multi-page responses, at most 4 and 24 MiB, by (generation, tag), evicting the least recently paged; a one-page response is complete in its first reply. Built (lc8-channel, [FFI and the runtime](#ffi-and-the-runtime)): a response held is also dropped once its last page is pulled, which `lkd-lc`'s planner never asks again | Decided |
| D13 | Deadlines, ordered client > core > shell > netd ([Constants](#constants)); G12's fetches serialized (history proof, then `0x13` to its last page, then `0x14`); a body fetch only while no account or storage read waits; at most 4 storage fetches in flight while a body fetch is; a paged job's age counted from its last page. Built with PROBE's 27 s body deadline: netd's, the shell's (a `FetchPage` 40 s besides: netd answers it from what it holds) and the UI's netd `TIMEOUT` and `ANSWER_WITHIN` by lc8-channel ([FFI and the runtime](#ffi-and-the-runtime)), the planner's at the stage-A merge. **Restated by D43 (LC9)**: the review's finding 12 showed these deadlines assumed one UI request and one body ahead of a fetch while the planner kept 16 in flight; netd now serves by rounds and says `Started`, the shell waits 120 s before it and the kind's deadline and 3 s after, and sends a fetch only while fewer than two are queued in netd, the planner keeps 2 in flight and at most 1 storage fetch beside a body, the core's backstops are 140 s and 155 s ([The deadline model (D43)](#the-deadline-model-d43)) | Decided; restated (D43) |
| D14 | One G12 job fetching bodies at a time (another transaction meanwhile: `Busy`); ahead and too old from the anchor's EL number without a fetch; settled once per (ask, hN) with a Prop witness, at most 8 kept, buffers dropped; refusals before both roots matched are refetched with `attempt + 1` up to `maxAttempts`; an answer only under a header named at answer time (the finalized one when N ≤ F ≤ N + 8191, else the anchor), with a history proof at it; the UI asks with `ask_within` up to `INCLUDED_WITHIN` (15 s), on a thread of its own, one ask at a time and one a refresh | Decided |
| D15 | Certificates where they apply, never optional: `Token`, `Pin` and `Pool` always (`Refused` if an answer would not fit, which the caps rule out in practice), `Included` when proved or too large; the UI re-checks every one and never shows green, gates on, or persists what it did not re-check | Decided |
| D16 | One Lean table, `LkdLc.Pins`, written by the base preparation with the development chain's rows measured; `lkd_verified::pins` transcribed separately and refined against it. Stage-A data fixes: commits on `build/lc78-base`, posted `BASE_A2` | Decided |
| D17, D18, D19 | USDC: balance = word ∧ (2²⁵⁵ − 1), bit 255 set shown frozen. USDT: slot 10 = 0, strict, gating sends. Linked libraries and verifiers pinned of their own, in `uses`; USDC's SignatureChecker not pinned (permit and `transferWithAuthorization` only) | Decided |
| D20 | Two-key reads at one anchor: `poolHead`, then `poolRoot(headValue)`; PP pool head words depth then size, Tornado's the index and leaf count; an Entrypoint of length 0 answers its head words | Decided |
| D21 | Pins on demand, as G14 says: the chain's whole set at session start (D37), whole again before a deposit, withdrawal, ragequit, stealth-send or registration review at the anchor current when it opens, and on an explicit refresh or a screen showing pin state, at most once an epoch; never on the automatic refresh. Token answers carry their pin's slots; only a proxy implementation's code hash comes from the set (EIP-6780 keeps it fixed) | Decided |
| D23, D24 | No anchor: today's reads, labelled the node's word; pools ignore caches. Development chain (31337) rows in the release tables, inert in release | Decided |
| D26, D27, D28 | Egress v8 restated as 10i (approvals' 10h merges beside it). `lkd-lc`'s halves of the composed theorems now (25t, 25u). An index the chain's table lacks: error 8 `NotPinned` | Decided |
| D29, D30, D31, D33 | The tracks, their contract and checks; verification once per checkpoint; master merged at the stage-A merge; the decision gate | Decided |
| D35 | The head cross-check by header: netproto `HeaderAt(N)` (`0x20`), answered `Header` (`0x94`, the RLP of `eth_getBlockByNumber(N, false)` on `Head`); `lkd_ui::proved::cross_check_block` compares its Keccak-256 with the anchored hash, caches the last 8 blocks and names no address; balances (verdicts unchanged), tokens, pins, pools and `Included`'s proving header use it | Decided |
| D36 | `Inclusion.verdict` and `settle` check the body's shape, then both roots, then look the hash up: `notInBlock`, `transaction` and `receipt` then mean the proved block says so, and settle without a refetch | Decided |
| D37 | Shared reads (pins, pools) never go out at the anchor of an `Account` read the UI made in the same refresh (balances, a token batch's `Token(i, owner)`): `proved::shared_wait()` holds them until one slot plus 0 to 6 s after the last `Account` answers (as built after the integration's review, also while an `Account` or `Token` read is in flight, from its first ask, `proved::AccountRead`: LC1's differential, a read `lkd-lc` still fetches); a review's batch waits too, and the review uses the last refresh's accounts. `MakeTokenSnapshot` reads only on `Account(owner)` | Decided |

### What this section overrides

Each passage is folded by its owner, or by the integration's docs pass:

- Open decisions 3, 4, 5, 19, 22, 23, 25, 26: the user's answers (integration).
- G12's step 5: kind 6 → 9; decision 23's "about 1.3 MB" → the measured sizes (lc8-phase2).
- G14: the gates (D1); the Failure states row "Pin unproved" and the helios table's G14 row (lc7-tokens-ui).
- G14 and G16, "a generator writes the Rust table, and a CI test checks they are equal" → the refinement (D16, lc7-egress).
- G19: "two copies, A and B … one pair per pinned pool and one for announcements" → one file per chain, two slots per region (lc7-cache, with 26a); "the same for every user …, so they name no one" → they name no address and show at rest which pools were synced (D34, lc7-pools-ui); "What it changes for an attacker" gains the two-fetch rule and a compromised UI (lc7-pools-ui); 25s's cache clause → 25v.
- The channel: "keys … reserved for LC7's and G9's typed key sets" → kind `0x15`; "`0x13` and `0x14` stay reserved" → built (lc7-wire). "netd's one-entry cache" → D12 (lc8-channel).
- FFI and the runtime, netd's loop: the 12 s, 25 s and 30 s deadlines → D13 (lc8-channel; the planner's lc7-scaffold). "A poll is skipped while a user query waits" → never for G12 (lc7-scaffold).
- Decision 18's as-built paragraph (an account proof at N) → D35 (lc7-egress).
- "Inclusion, as built", phase 2: egress 10g → v8, 10i (this commit).
- To confirm 1 and 2: answered by the survey; decision 24's cost stands, no periodic pin batch (integration).
- `06-tor.md`'s "a block with its transactions is never asked of a third party" → D4's exception (lc7-egress, in D4's commit).

All folded by 2026-10-27: each by its owner, and the open decisions, To confirm 1 and 2, decision 24's cost, the LC6 planner's 30 s, the composed theorems, Tested, not proved, the Testing passage's first deadlines and the Milestones by the final integration's docs pass.

### Frames

Common rules as in [Frame layouts](#frame-layouts); bodies include the tag. The anchor of every new answer is kind `2`, 103 bytes (45, then the anchored fields' 58), as an anchored `Account` writes it; its `final` field is 1 when the answer is at the finalized header.

**Queries**

| Tag | Query | Fields after the tag | Body | Answered by |
|---|---|---|---|---|
| `0x04` | `Token(i, owner)` (exists) | token index (2), owner (20) | 23 | `Storage.tokenLight` |
| `0x05` | `Pin(i)` (exists) | pin index (2) | 3 | `Storage.pinLight` |
| `0x06` | `Pool(i)` (exists) | pool index (2) | 3 | `Storage.poolLight` |
| `0x07` | `Included(h, N, i)` (exists) | tx hash (32), block (8), index (4) | 45 | `Included.includedLight` |
| `0x0a` | `CacheRead` | cache (2: kind, index), first item (4) | 7 | the shell |
| `0x0b` | `CacheAppend` | cache (2), offset (4), items (the rest, 1 to 65,529 bytes) | 7 + n | the shell |
| `0x0c` | `CacheCommit` | cache (2), count (4), block (8), root (32) | 47 | the shell |
| `0x0d` | `MakeTokenSnapshot(owner)` | owner (20) | 21 | `Storage.makeTokenSnapshot` |

`0x0e` is reserved for `MakeNameSnapshot` (D5), `0x0f` to `0x7f` for later. The core answers a cache frame `Unsupported`; the shell answers them before they reach it. `decodeQueryB` reads frames up to 51 bytes as lists, `CheckSnapshot` and `CacheAppend` as byte arrays.

**Answers**

| Tag | Answer | Fields after the tag | Body |
|---|---|---|---|
| `0x85` | `Token` | identity (72), anchor (103), token index (2), owner (20), contract (20), pin (1), detail (1), header length (4), header, account length (4), nodes, k (1: 1–8), k × (value (32), length (4), nodes) | 229 + H + A + Σ(36 + Sⱼ) |
| `0x86` | `Pin` | identity, anchor, pin index (2), verdict (1), detail (1), contract (20), code hash (32), implementation (20), implementation's code hash (32), header length (4), header, account length (4), nodes, k (1: 0–8), k × (value (32), length (4), nodes), implementation-account length (4), nodes | 284 + C, C = 13 + H + A + Σ(36 + Sⱼ) + I |
| `0x87` | `Pool` | identity, anchor, pool index (2), w (1: 1–8), w × word (32), header length (4), header, account length (4), nodes, w × (length (4), nodes) | 179 + 32w + C, C = 8 + H + A + Σ(4 + Sⱼ) |
| `0x88` | `Included` | identity, anchor, tx hash (32), block number (8), block hash (32), verdict (1), index (4), success (1), refusal (1), proving header length (4), header, N's header length (4), header, history-account length (4), nodes, history-slot length (4), nodes | 255 + C, C = 16 + P + Hₙ + A + S |
| `0x8b` | `CacheChunk` | identity, cache (2), committed count (4), block (8), root (32), first item (4), items (the rest) | 123 + n |
| `0x8c` | `CacheStored` | identity, cache (2), staged (4), committed (4), block (8) | 91 |
| `0x8d` | `TokenRecord` | identity, a snapshot record (the rest, at least 1 byte) | 73 + r |

`0x8e` and above are reserved. Values; every other value is refused (25o):

- Error code **8 `NotPinned`**: an index the chain's table lacks.
- `Token`: pin 0 matched, 1 upgraded, 2 mismatch, 3 condition failed, computed from its own slots at that anchor with the implementation's code not read (so never 4); detail = the condition's place (1–8) when pin is 3, else 0; k = 1 + the pin's slots, keys `tokenSlots` in order; header 1–2,048 bytes.
- `Pin`: verdict 0 matched, 1 upgraded, 2 mismatch, 3 condition failed, 4 implementation mismatch; detail as `Token`'s; implementation zero exactly when the pin has no proxy, else the address its slot holds; the implementation's code hash and its account's nodes present exactly when that address is the pinned implementation (zero and empty otherwise); k = the pin's slots (0–8), in `pinSlots` order.
- `Pool`: the words are the layout's head words, then the root word when `rootSlot` of the head value is defined; the slots' proofs in the same order.
- `Included`: verdict 0 proved, 1 ahead, 2 too old, 3 too large, 4 refused; the block hash nonzero exactly for 0 and 3; index and success zero unless 0; refusal 1–8 exactly for 4, numbered as `Inclusion.Refusal`'s constructors (1 `hashProof`, 2 `header`, 3 `body`, 4 `notInBlock`, 5 `transaction`, 6 `receipt`, 7 `transactionsRoot`, 8 `receiptsRoot`), else 0; both headers present exactly for 0 and 3 (1–2,048 bytes each), the history proofs exactly for 0 and 3 when N is not the proving block's number; the anchor names the proving block.
- `CacheChunk`: whole items of the region's size, none when the first item equals the committed count; root zero for a set. `CacheStored`: staged ≥ committed.

Certificates are never optional (D15): `Token`, `Pin` and `Pool` always, `Refused` if an answer would not fit (headers of at most 2,048 bytes and proofs of a few KB each rule that out in practice); `Included` as above.

Lean (`LkdLc.Wire`): `StorageCert {header account : ByteArray, slots : List (Bytes × ByteArray)}`; `TokenAnswer {anchor : Agreed, index : Nat, owner contract : Bytes, pin detail : UInt8, cert : StorageCert}`; `PinAnswer {anchor, index, verdict detail, contract codeHash impl implCode, cert : StorageCert, implAccount : ByteArray}`; `PoolCert {header account : ByteArray, slots : List ByteArray}`; `PoolAnswer {anchor, index, words : List Bytes, cert : PoolCert}`; `InclusionCert {anchorHeader header account slot : ByteArray}`; `IncludedAnswer {anchor, txHash, number, blockHash, verdict, index, success : Bool, refusal, cert : InclusionCert}`; `CacheChunk {cache count block root start items}`; `CacheStored {cache staged count block}`; `Answer.token id x t`, `.pin`, `.pool`, `.included`, `.cacheChunk id c`, `.cacheStored id c`, `.tokenRecord id r`; `Query.cacheRead cache start`, `.cacheAppend cache offset items`, `.cacheCommit cache count block root`, `.makeTokenSnapshot owner`. Rust (`lkd_verified::lc_wire`): the same names in Rust case; a struct with an optional part keeps a present flag and plain fields, never an `Option` of a struct (Aeneas has no model of its `Clone`).

**The channel**

| Kind | Request | Fields after the kind | Request (datagram) | Response |
|---|---|---|---|---|
| `0x13` | `ElBlock(attempt, tx, h)` | attempt (1), tx hash (32), block hash (32) | 66 (78) | `BlockBody`: header length (4: 1–2,048), header RLP, flag (1: `0` the transactions list follows, `1` too large, nothing follows), the transactions list RLP (the rest) |
| `0x14` | `ElReceipts(attempt, tx, h)` | as `0x13` | 66 (78) | the receipts list RLP |
| `0x15` | `ElStorage(attempt, h, keys)` | attempt (1), block hash (32), key set (1, then its arguments) | 37–75 (49–87) | `StorageProof`, one page: nonce (8), balance (16), storage root (32), code hash (32), account-proof length (4), nodes, key count (1: 0–8), per key value (32), length (4), nodes |

| Key set | Lean `Channel.KeySet` / Rust `KeySet`, const | Arguments | Request | Keys (`LkdLc.Pins`) | Contract | Group |
|---|---|---|---|---|---|---|
| 1 | `.pin i` / `Pin`, `KEYS_PIN` | index (2) | 37 | `pinSlots` | the pin's | `Shared` |
| 2 | `.pinImpl i` / `PinImpl`, `KEYS_PIN_IMPL` | index (2) | 37 | none | the pinned implementation | `Shared` |
| 3 | `.token i owner` / `Token`, `KEYS_TOKEN` | index (2), owner (20) | 57 | `tokenSlots` | the token's pin's | `Account(owner)` |
| 4 | `.poolHead i` / `PoolHead`, `KEYS_POOL_HEAD` | index (2) | 37 | `headSlots` | the pool's pin's | `Shared` |
| 5 | `.poolRoot i x` / `PoolRoot`, `KEYS_POOL_ROOT` | index (2), x (8) | 45 | `rootSlot x` | the pool's pin's | `Shared` |
| 6 | `.history n` / `History`, `KEYS_HISTORY` | n (8) | 43 | `historySlot n` | EIP-2935's | `Shared` (LC9, D38: issued by `lkd-lc` for `BlockHash` at the proving header's EL hash, which picks its endpoint; allocated on `Head` for D25, never issued there) |
| 7 | `.historyFor n tx` / `HistoryFor`, `KEYS_HISTORY_FOR` | n (8), tx hash (32) | 75 | `historySlot n` | EIP-2935's | `Broadcast(n_tx)` |

Key-set tags 0 and 8–255 are refused (8 and 9 reserved for D32's follow-up). `TooLarge` (7) also means receipts over `MAX_BLOCK_BODY` or a storage proof over a page. `lkd-lc-core`'s `request_len` reads the kind and, for `0x15`, the key-set tag at offset 34 (the ABI review). Lean `Fetch.elStorage (attempt : UInt8) (h : Bytes) (k : KeySet)`, `.elBlock attempt tx h`, `.elReceipts attempt tx h`; `StorageProof {account, nodes, slots : List (Bytes × ByteArray)}`; `BlockBody {header : ByteArray, txs : Option ByteArray}`. `lkd_lc_step`'s inputs and effects are unchanged.

**netproto** (UI ↔ netd, D35): request `0x20` `HeaderAt(N)`, the block number (8), 9 bytes: `egress::Request::Header(N)` (`eth_getBlockByNumber(N, false)`) on `Head`, one endpoint in turn; reply `0x94` `Header`, the header's RLP as netd re-encodes it (`reads::header_rlp`; the rest, 1–2,048 bytes).

### Egress v8, restated (10i)

`StorageByHash {chain, keys, hash}`: `eth_getProof(contract, slots, {"blockHash": hash})`, contract and slots from `pins::keys_of(chain, keys)`; groups: `Pin`, `PinImpl`, `PoolHead`, `PoolRoot` `Shared`; `Token{owner}` `Account(owner)`; `History` `Head`; `HistoryFor{tx}` `Broadcast(n_tx)`. `BlockByHash {block, tx, full}`: `eth_getBlockByHash(block, full)`; `BlockReceipts {block, tx}`: `eth_getBlockReceipts(block)`; both `Broadcast(n_tx)`, `n_tx` netd's broadcast number for `tx` as for `Receipt`, the transaction's hash never in the parameters, capped by `MAX_BLOCK_BODY`. `third_party_ok`: `StorageByHash` yes, except with `HistoryFor` keys; `HistoryFor`, `BlockByHash` and `BlockReceipts` only with D4's commit. `request_ok`: the chain is netd's and `keys_of` derives. `BlockByNumber` stays refused at third parties; `Header(N)` stays in `Head`. `Spec.Egress` mirrors it; `Public::number`'s new arms are under 10i's reviewer.

### Records

**`Included`**, journal kind 9, 120 bytes: kind (1), chain (8), tx hash (32), N (8), hN (32), index (4), success (1), final (1), outcome (1: 0 proved, 1 settled by nonce, 2 too old, 3 too large), checkpoint root (32). The codec refuses other outcomes; hN is nonzero exactly for 0 and 3, index and success zero unless 0, final 1 exactly for 0. `keyd` keeps every one; the UI ranks them (D3).

**`CacheMark`**, journal kind 10, 55 bytes: kind (1), chain (8), cache id (2), count (4), block (8), keccak-256 of the first `count` items (32). `keyd`'s `superseded` keeps the newest per (chain, cache), at most 64 a chain.

**Snapshot fact type 2**, in kind 7 after the type-1 facts (n counts both, at least 1; a type 1 after a type 2 refused): type (1), token index (2), owner (20), contract (20), the contract's account (88), proof length (4), nodes, k (1: 1–8), k × (value (32), length (4), nodes): 136 + P + Σ(36 + Sⱼ) bytes. Held exactly when the index names a token of the record's chain whose pin's contract is `contract`, `accountB` reads that account under the header's state root with the pin's code hash, the keys are `tokenSlots`, each value is `storageB`'s, and the pin's verdict with the implementation's code not read is matched. The implementation's code hash is not in the record: the session's pin set holds it (D21, EIP-6780). `MakeTokenSnapshot(owner)` answers `TokenRecord`: the owner's account fact and one token fact per pinned token whose fact holds at the finalized header, in the table's order (a token whose pin does not match there is left out). `CheckSnapshot`'s verdicts: one per fact, type-1 facts first.

### Pins, tokens and pools

`LkdLc.Pins` (Init only) is the one Lean table, written by the base preparation; `lkd_verified::pins` is transcribed separately and refined against it (`Refinement/Pins.lean`).

```lean
namespace Lkd.Lc.Pins
abbrev Bytes := List UInt8
def word (x : Nat) : Bytes := History.word x
def toNat (b : Bytes) : Nat := Spec.Rlp.beValue b
def pad32 (b : Bytes) : Bytes := List.replicate (32 - b.length) 0 ++ b
def mappingSlot (key : Bytes) (position : Nat) : Bytes := keccak (pad32 key ++ word position)
/-- `w + n` modulo 2²⁵⁶, the modulus written as a numeral. -/
def plus (w : Bytes) (n : Nat) : Bytes :=
  word ((toNat w + n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)
/-- `gates`: 1 deposits, 2 relayed withdrawals, 4 direct exits, 8 sends. -/
structure Condition where
  slot : Nat
  mask : Nat
  expected : Nat
  gates : Nat
structure Proxy where
  slot : Nat
  impl : Bytes
  implCode : Bytes
structure Pin where
  contract : Bytes
  code : Bytes
  proxy : Option Proxy
  conditions : List Condition
  uses : List Nat
structure Token where
  pin : Nat
  position : Nat
  mask : Nat
inductive Layout where
  | tornadoArray | tornadoMapping | ppPool | ppEntrypoint
structure Pool where
  pin : Nat
  layout : Layout
-- each deriving DecidableEq, Repr
def pins (chain : Nat) : List Pin     -- 1, 11155111, 31337; [] otherwise
def tokens (chain : Nat) : List Token
def pools (chain : Nat) : List Pool
def pinOf (c i : Nat) : Option Pin := (pins c)[i]?   -- tokenOf, poolOf likewise
def pinSlots (p : Pin) : List Bytes :=
  (p.proxy.map fun x => word x.slot).toList ++ p.conditions.map fun c => word c.slot
def tokenSlot (t : Token) (owner : Bytes) : Bytes := mappingSlot owner t.position
def tokenSlots (c : Nat) (t : Token) (owner : Bytes) : List Bytes :=
  tokenSlot t owner :: ((pinOf c t.pin).map pinSlots).getD []
def ethAsset : Bytes := List.replicate 20 0xee
def headSlots : Layout → List Bytes
  | .tornadoArray | .tornadoMapping => [word 3]
  | .ppPool => [word 5, word 4]
  | .ppEntrypoint => word 2 :: (List.range 4).map (plus (mappingSlot ethAsset 1))
def headValue : Layout → Nat → Nat
  | .tornadoArray, w | .tornadoMapping, w => w % 4294967296
  | _, w => w
def rootSlot : Layout → Nat → Option Bytes
  | .tornadoArray, x => if x < 100 then some (word (4 + x)) else none
  | .tornadoMapping, x => if x < 30 then some (mappingSlot (word x) 2) else none
  | .ppPool, x => if x ≤ 32 then some (mappingSlot (word x) 6) else none
  | .ppEntrypoint, x =>
    if 1 ≤ x ∧ x < 4294967296 then some (plus (keccak (word 2)) (3 * (x - 1))) else none
def historySlot (n : Nat) : Bytes := History.slot n
def balance (t : Token) (w : Nat) : Nat × Bool := (w &&& t.mask, w &&& t.mask != w)
inductive Verdict where
  | matched | upgraded (impl : Bytes) | mismatch | condition (k : Nat) | implMismatch
def verdict (p : Pin) (code : Bytes) (values : List Nat) (implCode : Option Bytes) : Verdict
def verdictByte : Verdict → UInt8   -- 0 to 4
def detailByte : Verdict → UInt8    -- k for `condition k`, 0 otherwise
```

`verdict`: the values are the pin's slots', in `pinSlots` order (an absent slot reads 0). The code not `p.code`: `mismatch`. A proxy whose slot's value v has `word v ≠ pad32 x.impl`: `upgraded` with v's low 20 bytes. `implCode = some c` with `c ≠ x.implCode`: `implMismatch` (`none`: not read). Then the first condition k, counted from 1, whose value v has `v &&& mask ≠ expected`: `condition k`. Otherwise `matched`. Masks are numerals: full 2²⁵⁶ − 1, USDC's 2²⁵⁵ − 1, an address's 2¹⁶⁰ − 1. `decide` checks literal fields only (contracts of 20 bytes, code hashes of 32, distinct contracts, indices in range, token contracts equal to `Spec.Tokens`): `word` is built on `Spec.Rlp.be`, defined by well-founded recursion, so slot widths come from one lemma, `x < 2^256 → (word x).length = 32`; literal keys are checked by `lkd-lc-pins-test` and Rust tests, never by `decide` (kernel Keccak).

Mainnet (1):

| # | Contract | Address | Code hash | Proxy slot → implementation, code hash | Conditions (slot: mask = expected, gates) | Uses |
|---|---|---|---|---|---|---|
| 0 | USDC | `0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48` | `0xd80d4b7c890cb9d6a4893e6b52bc34b56b25335cb13716e0d1d31383e6b41505` | `0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3` → `0x43506849d7c04f9138d1a2050bbf3a0c054402dd`, `0xcdfb7d322961af3acae7a8f7ee8b69c205b36f576cc5b077f170c7eb8ecbe3ea` | | |
| 1 | USDT | `0xdac17f958d2ee523a2206206994597c13d831ec7` | `0xb44fb4e949d0f78f87f79ee46428f23a2a5713ce6fc6e0beb3dda78c2ac1ea55` | | 10: full = 0, 8 | |
| 2 | DAI | `0x6b175474e89094c44da98b954eedeac495271d0f` | `0x4e36f96ee1667a663dfaac57c4d185a0e369a3a217e0079d49620f34f85d1ac7` | | | |
| 3 | WETH | `0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2` | `0xd0a06b12ac47863b5c7be4185c2deaad1c61557033f56c7d4ea74429cbb25e23` | | | |
| 4 | Tornado 0.1 ETH | `0x12d66f87a04a9e220743712ce6d9bb1b5616b8fc` | `0x67ae92ae22b390ba64cada35a7a9397da54f4a3a42beb33f3468517d42a875cc` | | 108: full = `0xce172ce1f20ec0b3728c9965470eaf994a03557a`, 1; 109: 2¹⁶⁰ − 1 = 0, 1 | 8, 9 |
| 5 | Tornado 1 ETH | `0x47ce0c6ed5b0ce3d3a51fdb1c52dc66a7c3c2936` | `0x4f4d8e2e727ad67793c89148d67918cc368fa4e5da9e1e6f039909d8db7ee8b8` | | as 4 | 8, 9 |
| 6 | Tornado 10 ETH | `0x910cbd523d972eb0a6f4cae4618ad62622b39dbf` | as 5 | | as 4 | 8, 9 |
| 7 | Tornado 100 ETH | `0xa160cdab225685da1d56aa342ad8841c3b53f291` | as 5 | | as 4 | 8, 9 |
| 8 | Tornado MiMC library | `0x83584f83f26af4edda9cbe8c730bc87c364b28fe` | `0x2769e338c9d60a078ef05dd9e03f5fa3e1df133f7da4494c5bcc83a71a9a9892` | | | |
| 9 | Tornado verifier | `0xce172ce1f20ec0b3728c9965470eaf994a03557a` | `0x77b17f6c3420b7608d193c7987c60c4559b6d3749c8939fb3a393aa5cb1ec716` | | | |
| 10 | PP Entrypoint | `0x6818809eefce719e480a7526d76bd3e561526b46` | `0xf15a07c54ab3420101c38795fc919a27ffb05f1a0049070ba3b8f10bae32af97` | `0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc` → `0x15e355024de1cdc74addea7ebdf98418ba5b1a2c`, `0xfb5c2ac0d0556e489bce13315892302150e6f682e6cab57e317ab1a4945af5e6` | `0xde3e59ea0eeb6a65f16dd826b7bdfb53723c09ad80c81d458bbf2e138d918523`: 2¹⁶⁰ − 1 = `0xf241d57c6debae225c0f2e6ea1529373c9a9c9fb`, 1 | |
| 11 | PP ETH pool | `0xf241d57c6debae225c0f2e6ea1529373c9a9c9fb` | `0xd7f3f10491a60c3295019ec7f7bfc4e70290d2bbc5278245b12dda8e93b066de` | | 1: `0xff` = 0, 1 | 12, 13, 14, 15 |
| 12 | PP withdrawal verifier | `0x022891f938ae7fdc8ab9ead0fbf50aba8c897d6d` | `0x54515096fff858166d381897047ecf92c8b6a595c01416cafa7b9b608670ab67` | | | |
| 13 | PP ragequit verifier | `0xa45aca8604a73d80c551faad6355a5c3a5565ec6` | `0x1045f87f241bb626b24e0156a478cc0a1d018ad7850c728fd93f10c4b03b27cd` | | | |
| 14 | PP library | `0xe393dd7287db9982e6f845824854baf8b8e823af` | `0x3398947113cbb65ddfd4bfc2357b43c777e8e04e9fbd674d8db463cc09767161` | | | |
| 15 | PP library | `0x8ffda7ed8b4ad98c2c34f54b76821711f4a6f2c5` | `0x4add57adf71c731d63adc03c0d0cb5a99996e24e58d45641809dc6fb8a379372` | | | |
| 16 | Multicall3 | `0xca11bde05977b3631167028862be2a173976ca11` | `0xd5c15df687b16f2ff992fc8d767b4216323184a2bbc6ee2f9c398c318e770891` | | | |
| 17 | ERC-5564 announcer | `0x55649e01b5df198d18d95b5cc5051630cfd45564` | `0x80ed491c57edc6d92b5a85cc7db2dfeb40bbab52476b5b09b9b21c5c907b77c4` | | | |
| 18 | ERC-6538 registry | `0x6538e6bf4b0ebd30a8ea093027ac2422ce5d6538` | `0x359de1db41b37ccad6adb8203bb46fd717b1ace6e1f336ba0f9f7290aa586dd3` | | | |
| 19 | EIP-2935 history | `0x0000f90827f1c53a10cb7a02335b175320002935` | `0x6e49e66782037c0555897870e29fa5e552daf4719552131a0abce779daec0a5d` | | | |

Tokens (the order of `lkd_verified::tokens`): 0 USDC (pin 0, position 9, 2²⁵⁵ − 1), 1 USDT (1, 2, full), 2 DAI (2, 2, full), 3 WETH (3, 3, full). The wallet's token 4, stETH (`0xae7a…fe84`, master's da653021), is **not pinned** (`unpinnedTokens`, `lkd_verified::pins::unpinned_token`), by the user's choice of 2026-10-28: a proxy Lido can upgrade, rebasing. lkd-lc answers its `Token(4)` `NotPinned` (error 8) and the UI never asks it; its balance is one endpoint's word (a quorum's until 2026-10-28), labelled so ("the endpoints' agreement, not proved: the light client does not pin stETH", as `token_proofs::label` still words it), never as proved; a stETH send asks D1's acknowledgment for a contract not pinned ("stETH: not pinned in this release"). stETH: no fiat value, by the user's choice of 2026-10-28; its balance is the endpoints' agreement, not proved. The wallet's token 5, wstETH (`0x7f39…2Ca0`, spec/19's T5, 2026-10-28), has no row either (`unpinnedTokens` = `[4, 5]` on mainnet) and is treated as stETH is: `Token(5)` `NotPinned`, its balance one endpoint's word, labelled so, a send of it asking the acknowledgment ("wstETH: not pinned in this release"), and no fiat value. The table's tokens are indexed by the wallet's order, so a row for wstETH would need one for stETH first; pinning it (its code is not a proxy's, code hash `0x6301…0557`) is left to a reviewed change of the pin table's data. Pools: 0–3 Tornado (pins 4–7, `tornadoArray`), 4 PP pool (11, `ppPool`), 5 association set (10, `ppEntrypoint`). USDC's linked SignatureChecker is not pinned (permit and `transferWithAuthorization` only).

**Sepolia (11155111)**: 0 USDC `0x1c7d4b196cb0c7b01d743fbc6116a902379c7238`, `0xcd3f29e2ea9c61dadd48bfeaf8b2884b6de9dfee7bf45329452c4c33d0868ceb`, the same ZeppelinOS slot → `0xda317c1d3e835dd5f1be459006471acaa1289068`, `0xf4898b096a273d86cda13cce6503404da4005565fae6026a94919b231229d85b`; 1 WETH `0xfff9976782d46cc05630d1f6ebab18b2324d6b14` (the ERC-7730 registry's, the token list's since 2026-10-27; re-pinned 2026-10-28 at block 12,012,046 `0xa2c0b447…8512`, OnFinality and 0xRPC by block hash in agreement, WETH9 of another build), `0xc864e10689f2da18833652a3b075d43106e87f0f90d95ee64f6f0b33bc026083`, `balanceOf` at position 3 (four holders' `balanceOf` equal to their word at slot 3 and at no other position from 0 to 7); 2 LINK `0x779877a7b0d9e8603169ddbd7836e478b4624789`, `0xcafbd9135200b24454a9ffcac5a8db40947a17f8a8a542062d0f1fb48bd8b269`; 3 Tornado 0.1 `0x8c4a04d872a6c1be37964a21ba3a138525dff50b`, `0x443e47bab099f77f1926bc8404353e9ddcfa0cd62e4416194332e852e6af1075`; 4 Tornado 1 `0x8cc930096b4df705a007c4a039bdfa1320ed2508`, `0x4a267fe8a40ba50b7df69bf49a072d8dccf2fc41cc709978b21141a905be1f61`; 5 Tornado 10 `0x8d10d506d29fc62abb8a290b99f66db27fc43585`, `0xab78e17f89cea1d52ef1e52019b572bc55b4b0e667e9184e4e080d53cc1c0450` (3–5 use 6, 7); 6 verifier `0xae523682eb597e057aca3dc009161a122656f00e`, `0x956c4058e64363b96e1b60ad7e0a70678da96f24fee78f1d9740640a19084034`; 7 hasher `0x20bc314fc55345d74235731b6c0cd57ede6cdf2f`, `0x2769e338c9d60a078ef05dd9e03f5fa3e1df133f7da4494c5bcc83a71a9a9892`; 8 Multicall3, 9 announcer (mainnet's addresses and hashes); 10 registry `0x6538e6bf4b0ebd30a8ea093027ac2422ce5d6538`, `0x6d369f3703602b1af1b4d58aa6316d715a69f871b93a2ea126dbd1e4a58c4348`; 11 history. Tokens 0 USDC (0, 9, 2²⁵⁵ − 1), 1 WETH (1, 3, full), 2 LINK (2, 0, full). Pools 0–2 Tornado (pins 3–5, `tornadoMapping`).

**Development chain (31337)**, inert in release: 0 USDC, 1 WETH, 2 LINK at Sepolia's addresses (WETH `0xfff9…6b14`) with WETH9's code (`crates/e2e/fixtures/weth9.hex`, `0x9efe…98ee`, the code of Sepolia's earlier WETH `0x7b79…e7f9`), no proxy; 3 Multicall3, 4 announcer, 5 registry with the Keccak-256 of `crates/e2e/fixtures/{multicall3,announcer,registry}.hex`; 6 history (anvil runs no EIP-2935: the contract holds no code until a scenario plants the EIP's, as `lc-mined` does). Tokens 0–2 (pins 0–2, position 3, full). Rows 7–16 and pools 0–3, measured by the base preparation on `lkd-e2e --dev-chain` on 2026-10-27 (fixed deployer keys and nonces: Tornado's key `0x…0d3b10` deploys the hasher and the verifier at nonces 0 and 1; Privacy Pools' `0x…0ba1e5` the Poseidon libraries, the two verifiers, the implementation, the proxy and the pool at nonces 0 to 6):

| # | Contract | Address | Code hash | Proxy, conditions, uses |
|---|---|---|---|---|
| 7 | Tornado 0.1 | `0x8c4a04d872a6c1be37964a21ba3a138525dff50b` | `0x21f9a0e355af4f8ff4e6849f9cb9aa9e6a67ae846da02e280697d2d88e8707a5` | uses 9, 10 |
| 8 | Tornado 1 | `0x8cc930096b4df705a007c4a039bdfa1320ed2508` | `0x32611140c243cfec38c19d85704c6067e50cc7e5c5179f6f6630964477eead9b` | uses 9, 10 |
| 9 | Tornado verifier | `0xe68ffa4ed4509803a7c7b93268c9f7b30f9f9ebf` | `0x956c4058e64363b96e1b60ad7e0a70678da96f24fee78f1d9740640a19084034` | |
| 10 | Tornado hasher | `0x9d463e3d9c8d8e24c8ccc43e30c8ba16ab2fc6fe` | `0x2769e338c9d60a078ef05dd9e03f5fa3e1df133f7da4494c5bcc83a71a9a9892` | |
| 11 | PP Entrypoint | `0xb79e5b2e35347dbbd3bf5b8094c9824d3ce6cf88` (`pp::ENTRYPOINT_DEVNET`) | `0xf15a07c54ab3420101c38795fc919a27ffb05f1a0049070ba3b8f10bae32af97` | EIP-1967 → `0xbba8fcb39bb3f22e23e0f00c469496b37ec1ba3d`, `0x19e58f0b1e8c483a4936800268fb428ef8bed355f6fb7b14760244355055c8b3`; condition `mappingSlot ethAsset 1`: 2¹⁶⁰ − 1 = `0x48af21a12cc3d05eb6d1bd24722788cf28eff185`, gates 1 |
| 12 | PP pool | `0x48af21a12cc3d05eb6d1bd24722788cf28eff185` (`pp::POOL_DEVNET`) | `0xfbc76f386891642770f559a840755f9acef1bca2450d8113d6c9143a4a6ffe77` | condition 1: `0xff` = 0, gates 1; uses 13–16 |
| 13 | PP withdrawal verifier | `0x00ec4c8a040760aac93540bed36748d817e4cff4` | `0x54515096fff858166d381897047ecf92c8b6a595c01416cafa7b9b608670ab67` | |
| 14 | PP commitment verifier | `0xc5cd4024d9200fe102fbf59b602aaac27406ffc9` | `0x1045f87f241bb626b24e0156a478cc0a1d018ad7850c728fd93f10c4b03b27cd` | |
| 15 | Poseidon T3 | `0xdf377675fb02f5c44f71a694fb16b25d490a7d63` | `0x688a7ba21a7b52f35df8f834d6ec41ff8745ddcb1af77763c8eeeb5383f32ecc` | |
| 16 | Poseidon T4 | `0xd52ca8a1c2906d107617396926f598950b54d774` | `0x02fc5846fe36e03be738753df3666852340513108bf832fe9158768f45c495e2` | |

Pools: 0 (pin 7), 1 (pin 8), both `tornadoMapping` (measured: the root `getLastRoot()` returns is in the mapping at slot 2 under the low 32 bits of slot 3, before and after a deposit); 2 PP pool (12, `ppPool`); 3 association set (11, `ppEntrypoint`), both layouts read back as `currentRoot()` and `latestRoot()` after two deposits and a posted root.

Checked by `lkd-lc-pins-test` and Rust tests, never by `decide`: `mappingSlot (word 14) 6 = 0xaca6cdb4b5fe0ec50731a73f714dd191dc1911bfeb3f9eeb9e94ed0f6065ef8d`; `mappingSlot ethAsset 1 = 0xde3e59ea0eeb6a65f16dd826b7bdfb53723c09ad80c81d458bbf2e138d918523`; `plus (keccak (word 2)) (3 * 3291) = 0x405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb815f`; Sepolia `mappingSlot (word 20) 2 = 0x50d9dffd10eb4437a15e8bb1c50afee98ea231805f136fb9a057e7aaeec448ae`.

### `lkd-lc`

**The scaffold (lc7-scaffold).** `step` lives in `LkdLc/Step.lean` and dispatches `Token`, `Pin`, `Pool`, `MakeTokenSnapshot` to `Storage.tokenLight s conn i owner`, `pinLight s conn i`, `poolLight s conn i`, `makeTokenSnapshot s conn owner`, `Included` to `Included.includedLight s conn h n i`, the cache frames to `Unsupported`, the rest as before; `LkdLc/Ffi.lean` exports `stepC` over it (the ABI review). `PlanCommon.lean` (namespace `Lkd.Lc.Plan`) holds `Ctx` (with `chainId`), `Failure`, `maxAttempts`, `attemptByte`, `errorMs`, `jobMs := 50000`, `bodyJobMs := 60000`, `timedOut`, `notSsz`; `Lc.fetchMs := Plan.jobMs`; `PlanStorage` and `PlanIncl` import neither `Plan` nor `Lc`. Fixed statements, proved for the stubs by lc7-scaffold and again by the stage-B owner:

```lean
def PlanMoves (s s' : State) : Prop :=
  ∃ l p t ph, s.light = some l ∧
    s' = { s with light := some { l with plan := p }, nextTag := t, lastPhase := ph }
def HandlerMoves (s : State) (conn : Nat) (r : State × List Effect) : Prop :=
  (r.1 = s ∨ PlanMoves s r.1) ∧ ∀ e ∈ r.2, (∃ an, e = .answer conn an) ∨
    ∃ t f, e = .fetch t f ∧ Plan.fetchOk f = true ∧ ∀ w ∈ s.waits, w.tag ≠ t
def StorageAnswer : Answer → Prop
  | .error _ _ | .pending _ _ | .token _ _ _ | .pin _ _ _ | .pool _ _ _ | .tokenRecord _ _ => True
  | _ => False
def InclAnswer : Answer → Prop
  | .error _ _ | .pending _ _ | .included _ _ _ => True | _ => False
-- for H ∈ tokenLight, pinLight, poolLight, makeTokenSnapshot (StorageCore) and includedLight (InclCore):
theorem H_moves (s conn args) : HandlerMoves s conn (H s conn args)
theorem H_good {s} (hs : Inv s) {conn} (hc : conn < 2 ^ 32) (args) : Good (H s conn args)
theorem H_answers (s conn args) {c an} (h : .answer c an ∈ (H s conn args).2) : StorageAnswer an
  -- InclAnswer for includedLight
structure PlanStorage.Read where
  hash : Bytes          -- the EL hash it reads at; lc7-core's further fields all have defaults
def PlanStorage.maxReads : Nat := 48
def PlanStorage.waiting (rs : List Read) (named : List Bytes) : Bool
def PlanStorage.headers (rs : List Read) : List Bytes
def PlanStorage.cands (ctx : Plan.Ctx) (rlpOf : Bytes → Option ByteArray) (rs : List Read) :
  List Wire.Channel.Fetch
def PlanStorage.deliver (ctx : Plan.Ctx) (rlpOf : Bytes → Option ByteArray) (rs : List Read)
  (f : Wire.Channel.Fetch) (bs : ByteArray) : List Read
def PlanStorage.fail (now : Nat) (rs : List Read) (f : Wire.Channel.Fetch) (code : UInt8) : List Read
-- deliver_length, fail_length: rs.length ≤ maxReads → result.length ≤ maxReads
structure PlanIncl.Job where
  hash : Bytes          -- the proving header's EL hash; lc8-phase2's further fields all have defaults
def PlanIncl.Ok (j : Option Job) : Prop
-- waiting, headers, cands, deliver, fail with PlanStorage's shapes over Option Job; ok_none, deliver_ok, fail_ok
```

`candidates` = read ++ boot ++ grid ++ catchUp ++ storage ++ incl ++ poll; polls wait while an account or storage read waits, never for G12; EL headers are asked while account, storage or G12 reads want them (`wantBlocks`: wanted first, then held blocks still named, at most `maxBlocks`); `deliver` and `fail` send `historyFor`, `elBlock`, `elReceipts` to `PlanIncl` and other `elStorage` to `PlanStorage`; a body fetch is issued only while no account or storage read waits, and at most 4 storage fetches are in flight while a body fetch is; `expire` uses `bodyJobMs` for bodies and counts a paged job's age from its last page. `Plan.Bounded` gains `storage` and `incl`. lc7-scaffold re-proves `Evidence.step_ok`, `Anchored.step_anchored` and `Snapshot.snapshot_answers` through one dispatch lemma; `record_sound` keeps its statement (`TokenRecord` is another answer). A plumbing test (`plumbingCases` in `lkd-lc-plan-test`) exercises the header plumbing with a `{ hash := … }` read and job in stage A. In stage B lc7-core owns fixes to the scaffold's files and posts them as `SCAFFOLD_FIX`; lc8-phase2 merges them.

**Storage reads (lc7-core).** A read is a key set at an EL hash, checked as an `ElProof` is: the endpoint's account and values must equal what `Facts.storage` reads under the bound header (25j, 25k), else asked again (`maxAttempts`), then `Refused`, or `Unreachable` for `errorMs`. `Pin(i)`: `pin i` and, for a proxy, `pinImpl i` at the anchor. `Token(i, owner)`: `token i owner` at the anchor. `Pool(i)`: `poolHead i`, then `poolRoot i (headValue …)` at the same anchor (an Entrypoint of length 0: head words alone). `MakeTokenSnapshot(owner)`: at the finalized header, the owner's account read and every pinned token's `token` read, all on `Account(owner)`, one record. Unknown index `NotPinned`; no anchor `NotAnchored`; else `Pending`. **25t**, in `anchored_sound`'s shape (`LkdProofs.Lc.Storage`): for a `.token id x t` answer in a run from `init c`, the identity is the state's; the query was `Token(t.index, t.owner)`; a store the run reached holds an anchor signed by at least two thirds of its committee whose header `Anchor.bind` keeps as `hdr`, with `t.cert.header` its RLP; `Spec.Mpt.accountB` reads `t.contract`'s account under `hdr.stateRoot` from `t.cert.account`; each value is `Spec.Mpt.storageB`'s at `tokenSlots c tok t.owner` under that account's storage root; and `t.pin = verdictByte (verdict p acct.codeHash values none)`, the implementation's code not read. `pin_sound` likewise with `pinSlots` and, when read, the implementation's account (`some implCode`); `pool_sound` with `headSlots` then `rootSlot (headValue …)`; `tokenRecord_sound` as `record_sound`, at the finalized header, each token fact held.

**G12's job (lc8-phase2).** `Included(h, N, i)`: no anchor `NotAnchored`; another transaction's job fetching bodies `Busy`; `N > A` ahead, `A > N + 8191` too old, from the anchor's EL number, no fetch. The proving header P is the finalized one when N ≤ F ≤ N + 8191 (final), else the current anchor. The job fetches, serialized: `.elStorage a hP (.historyFor N h)` (unless N is P's number), then `.elBlock a h hN` to its last page, then `.elReceipts a h hN`. Flag 1 or a receipts `TooLarge` gives body `none`. `Inclusion.settle q hN header body` runs once, its result kept with a Prop witness (`∃ txb rcb, …`) and N's header, buffers dropped, at most 8 kept. D36: `verdict` and `settle` check the body's shape, the transactions root, the receipts root, then look the hash up, then the envelopes; refusals before both roots matched are fetched again with `attempt + 1` up to `maxAttempts`, the others settle at once. An answer needs a history proof at a header named at answer time (fetched when asked and the anchor moved) and a settled result for that hN; the final answer refetches only the history proof. `verdict_eq_settle`: `verdict` depends on the anchor only through `hashOf` and `final`. `verdict_notInBlock`: N's header is bound to hN, its transactions list rebuilds its `transactionsRoot`, and no item hashes to h. **25u** `included_sound`: a `.included id x a` with verdict 0 in a run gives the identity; the query `Included(a.txHash, a.number, _)`; a reached store and a header `hdr` that `Anchor.bind` keeps for the store's anchor (`x.final = 0`, two thirds signed) or its finalized header (`x.final = 1`), with `a.cert.anchorHeader` its RLP; the verdict's anchor is `⟨hdr's EL hash, hdr.stateRoot, hdr.number, x.final⟩`; `hashOf` of it with the certificate's history proof (`.anchor` when N is `hdr.number`) is `some a.blockHash`; and `∃ txb rcb, Inclusion.verdict ⟨…⟩ ⟨a.txHash, a.number, hint⟩ hp a.cert.header (some (txb, rcb)) = .proved a.index a.success (x.final = 1)`.

### netd

`lc_storage.rs` (lc7-core): `KeySet` to `egress::Keys`, endpoint `el_endpoint(key, attempt)` (the owner for a token, the contract otherwise; for `historyFor` `g12_endpoint(tx, attempt)`, as G12's bodies: first the endpoints that took the transaction's broadcast this session, then the one the transaction's hash picks), `Node::storage_by_hash`, parsed only through `reads::storage_part` and `reads::proof_bytes` (they keep master's `proof_nodes`), address and keys checked in order, over a page `TooLarge`. `lc_bodies.rs` (lc8-phase2): `el_block` by hash, over `MAX_BLOCK_BODY` the header-only request on the same group and endpoint (`header_rlp` must hash to hN) and flag 1; `el_receipts`; `envelopes.rs` (lc8-prep) re-encodes as `fetch.py` does. `lc.rs` (lc8-channel): held responses (D12), deadlines (D13). `rpc.rs`, `http.rs`, `server.rs` (lc7-egress): methods, `Public::number`, caps, `Failure::TooLarge`, `HeaderAt`.

### The public caches (G19)

`<home>/lc/<chain>.cache`, opened in serve mode before the sandbox (`O_RDWR|O_CREAT|O_NOFOLLOW|O_CLOEXEC`, 0600, an exclusive `flock`; otherwise no caches); a 4 KiB header (`LKDLCCA1`, version 1, chain, region table; a different table resets the slots); per region (`lkd_verified::cache::regions`) two 128-byte slots (`LKDC`, sequence 8, count 4, block 8, root 32, digest 32), padding to 4 KiB, items append-only. Kinds and items: the allocations' cache table. Mainnet's file is about 140 MiB, sparse; `RLIMIT_FSIZE` rises to cover it, `pread64` is allowed, and the evidence writer's own bounds are tested (26a restated). The shell (lc8-channel) answers `CacheRead` from committed items, `CacheAppend` at the staged end or 0, `CacheCommit` with count = staged, drops a closed connection's staging, answers `Busy` for another live connection's transfer; errors `Malformed`, `Unsupported`, `Refused`, `Busy`. The UI (lc7-pools-ui) checks per D8, commits per D9, writes a mark after each commit, offers a rescan. **What remains (25v, N1)**: a log every fetch missed; a compromised UI can append set items with a matching mark (it writes both), which stand until a rescan; trees and ASP leaves stay root-checked. Labels say spent sets and announcements rest on the endpoints and the mark.

### The head cross-check (D35)

`proved::cross_check_block(netd, number, hash, finalized)`: netproto `HeaderAt(number)`; the reply's Keccak-256 equal to `hash` agrees; another hash is a verifier disagreement at or below `finalized` (red, the value unproved) and "your node disagrees at block N (not final)" above it (yellow); no answer leaves it unchecked (not green). The last 8 (number, hash) verdicts are cached. Balances use it in place of the account proof at N (verdicts and labels unchanged); tokens, pins and pools before showing green or gating, one check per block of a batch (`proved::CrossChecks`: the answers at one block share it, and once one goes unanswered no other block of the batch is asked, so an EL route that does not answer costs a batch one wait for netd, not one per answer); `Included` before persisting a proved outcome. It names no address.

### The UI

- lc7-tokens-ui (`pins.rs`, `token_proofs.rs`): pin batches (D21, D37), D1's table in the TUI, the window and the CLI, token values with provenance, Settings' Pins row, token snapshots (D22), the doctor's line for reth (`--rpc.eth-proof-window` at least 256 on an own-node route with a light client). `needs(flow)`: a deposit the pool's pin (PP: the Entrypoint and the pool) and their uses; a PP relayed withdrawal the Entrypoint, the pool and their uses; a Tornado withdrawal the pool and its uses; ragequit the PP pool and its uses; a stealth send Multicall3 and the announcer; registration the registry; a token send the token's pin.
- lc7-pools-ui (`pool_proofs.rs`, `cache.rs`): proved roots replace `IsKnownRoot`, `GetLastRoot`, `PpCurrentRoot`, `PpLatestRoot`, `PpAssetConfig` reads when anchored; the caches (D8, D9, D6); Settings' Public caches row with D34's disclosure and the rescan.
- lc8-ui (`included.rs`, `history.rs`): states "mined (the node's word)", "seen, not yet proved", "mined in block N at index i, succeeded (proved)" or "failed (proved)", "(proved, not final)", "proved under an earlier checkpoint", "not provable: more than 8191 blocks back", "the node mislocated it", "inclusion not provable: block N too large to fetch", "settled by nonce, inclusion unproved", "inclusion not checked on public endpoints (your choice)", "the light client refused the node's receipt: <check>" (red); D3's and D7's persistence; `lkd status` exits 0, 5, 3 and **7** for a refused receipt.

### Constants

Ordered client > core > shell > netd. netd: `EL_DEADLINE` 12 s, `BODY_DEADLINE` 20 s (`0x13`, `0x14`), `BEACON_DEADLINE` 8 s, `LONGEST_DEADLINE` 20 s; the UI's netd `TIMEOUT` 10 + 20 + 3 = 33 s. The shell's per kind (one UI request 10 s + one body ahead 20 s + its own + 3 s): beacon 41 s, EL (`0x10`–`0x12`, `0x15`) 45 s, bodies 53 s. The core: `jobMs` 50 s, `bodyJobMs` 60 s, `Lc.fetchMs` = `jobMs`. The UI: `ANSWER_WITHIN` 55 s, `MAKE_WITHIN` 55 s, `PIN_BATCH_WITHIN` 60 s, `INCLUDED_WITHIN` 15 s; `ANCHOR_WITHIN` stays 12 s (a refresh during a body download may show balances yellow, "still fetching", once), `CHECK_WITHIN` 60 s, the shell's `IDLE` 10 s. If PROBE puts the p95 of a body over Tor above 15 s, `BODY_DEADLINE` = ⌈4/3 · p95⌉ and every derived constant, posted with BASE_B. PROBE measured 19.80 s ([As built, lc8-prep](#lc8-prep)), so `BODY_DEADLINE` is 27 s and, each layer keeping its margin over the one below: netd's `LONGEST_DEADLINE` 27 s; the UI's netd `TIMEOUT` 10 + 27 + 3 = 40 s; the shell's beacon 48 s, EL 52 s, bodies 67 s; the core's `jobMs` 57 s and `bodyJobMs` 74 s, `Lc.fetchMs` = `jobMs` (set at the stage-A merge); the UI's `ANSWER_WITHIN` and `MAKE_WITHIN` 62 s, `PIN_BATCH_WITHIN` 67 s; `INCLUDED_WITHIN`, `ANCHOR_WITHIN`, `CHECK_WITHIN` and `IDLE` unchanged. **Since D43 (LC9)**, in `lkd_verified::deadlines` and ordered by `Refinement.Deadlines`: netd's 8, 12 and 27 s unchanged (`BEACON_MS`, `EL_MS`, `BODY_MS`), its turn by rounds with `Started`; the shell's `QUEUE_LIMIT_MS` 120 s before `Started`, then netd's deadline and `MARGIN_MS` (3 s): 11, 15 and 30 s, a `FetchPage` 123 s, at most two of its fetches queued in netd (a timed-out one counted until its reply or 240 s); the core's `jobMs` 140 s, `bodyJobMs` 155 s, `Lc.fetchMs` = `jobMs`, `maxJobs` 2, `perStep` 2, `maxStorageWithBody` 1; the UI's netd `TIMEOUT` `UI_NETD_TIMEOUT_MS` (40 s, unchanged), its other windows unchanged, now budgets rather than layers above the shell's.

### Invariants

10i (lc7-egress, second reviewer, with `HeaderAt`), 25k and 25s (lc7-facts), 25o and 25q (lc7-wire-rs, with lc7-wire's Lean statements), 25r (lc7-scaffold; cache frames lc8-channel), 25t new after 25s (lc7-core), 25l restated with D36 and 25u new after 25l (lc8-phase2), 25v new after 25q (lc7-cache; shell lc8-channel; UI lc7-pools-ui, with what remains), 25w new after 25v (lc7-tokens-ui, the gates, mixing review), 26a (lc7-cache, second reviewer), journal codec and the new rows Journal Included records (UI clause lc8-ui) and Journal cache marks (lc8-prep, storage review).

### Tests

`lkd-lc-pins-test` (lc7-facts): one recorded block per chain from two providers whose block hashes agree. Planner cases and the plumbing test (`lkd-lc-plan-test`: lc7-scaffold, lc7-core); G12 job cases and the whole job under 1 s on the two largest kept blocks, failing only with `--budget` (lc8-phase2, `lkd-lc-incl-test`; `just lc` prints the times). e2e: `lc-history`; `lc-tokens`, `lc-pins`, `lc-pools`; `lc-mined`; `lc-tokens-ui`; `lc-pools-ui`, `lc-cache`; `lc-mined-ui`, `lc-netd-busy`, `lc-killed-mid-body`. `just lc` runs `lkd-ssz-test`, `lkd-lc-incl-test`, `lkd-lc-pins-test` too.

### Second reviewers

Egress 10i with `Public::number` and `HeaderAt`; the ABI: lc-core's `request_len`, `LkdLc/Ffi.lean` exporting `Step.step`; storage: journal kinds 9 and 10, `superseded`, fact type 2, the persistence rules of `lkd_ui::included` (D3, D7); sandbox: 26a, the cache file and store, the shell's cache frames; mixing: D1's gates, G16 in privacy flows, the caches' checks, every caller of `cross_check_block`; the pin table's data, re-derived from a source independent of the survey; every restated Lean statement (lean-gate skipped for now).

**Independent review pass 2026-10-28** (ABI/unsafe, storage, egress, sandbox, Lean statements, mixing: 12 findings, 9 confirmed, fixed in build/lc-master; pin table re-derived from MEV Blocker, 0xRPC, Tenderly, OnFinality: 0 mismatches, .tools/scratch-lcpins/REPORT.md). The nine, each fixed in its own commit: egress, an install with no salt (every master install) drew a fresh one per netd start (decision 11; `lkd settings` and `lkd start` now write one once); storage, `rewrite()` fell back to the unlinked old journal after a successful rename, and Settings' rescan left `lkd-lc`'s cache file, so another wallet process could commit on top and undo it; sandbox, `sendto` to pathname datagram sockets on the channel (now `dest_addr` null only, Landlock ABI 9), and the missing `io_uring` denial (fixed by fd51fed4 before this pass); Lean statements, 25c's `PairingCheckIs` unsatisfiable over every point (now over G1 and G2, with `HashInG2` named), 25g citing the removed `step_no_persistConflict` (`step_persistConflict` now composed through the ingest chain), `Ui.gate_pass_sound` dropping `Configured`; mixing, the Contracts line naming the batch's newest block. The three others were refuted by their skeptics (`.tools/scratch-lcland/confirmed.json`). This pass is no substitute for the human second reviewer `AGENTS.md` asks for, which is still owed for every item above, as for master's other landings.

### Tracks and what they own

Stage A off BASE_A: lc7-wire (`lc7/wire`, Lean frames), lc7-wire-rs (`lc7/wire-rs`, Rust frames and the UI client), lc7-scaffold (`lc7/scaffold`), lc7-facts (`lc7/facts`), lc7-egress (`lc7/egress`), lc8-prep (`lc8/prep`), lc7-cache (`lc7/cache-store`). The stage-A merge merges master first. Stage B off BASE_B: lc7-core (`lc7/core`), lc8-phase2 (`lc8/phase2`), lc8-channel (`lc8/channel`), then B1 (their merge, checked), and lc7-tokens-ui (`lc7/pins-tokens-ui`), lc7-pools-ui (`lc7/pools-ui`), lc8-ui (`lc8/ui`), which merge B1 before their new scenarios. File ownership: the allocations' module table.

### Working agreements

**Track setup** (ID, BRANCH, BASE and SRC from the brief; stage A: `build/lc78-base`, `track-lc78-base`; stage B: `build/lc78-a`, `track-lc78-a`):

```bash
export LKD_AENEAS=74aabd5; . /projects/leanKohakuDesktop/.tools/env.sh
T=/projects/leanKohakuDesktop/.tools; WT=$T/track-$ID; S=$T/$SRC
export CARGO_TARGET_DIR=$T/target-$ID TMPDIR=/tmp/lt-$ID CARGO_BUILD_JOBS=4 LEAN_NUM_THREADS=8
H=$T/lc78-heavy.sh; E=$T/lc78-e2e.sh
git -C /projects/leanKohakuDesktop worktree add -b $BRANCH $WT $BASE
mkdir -p $TMPDIR $WT/proofs/.lake
cp -a $S/proofs/.lake/build $S/proofs/.lake/config $WT/proofs/.lake/
ln -s $T/track-lean435/proofs/.lake/packages $WT/proofs/.lake/packages
cp -a $S/proofs/core/.lake $WT/proofs/core/; cp -a $S/proofs/tests/.lake $WT/proofs/tests/
cp -a $S/proofs/LkdProofs/Extraction $WT/proofs/LkdProofs/
touch $WT/crates/core/build.rs $WT/crates/lc-core/build.rs
```

The cargo target is made by the stage's preparation; a track never copies one or uses another's (lc7-wire has none). `proofs/LkdProofs/Extraction` is git-ignored: after any change in `crates/verified`, `CARGO_TARGET_DIR=$T/target-$ID-charon $H just extract`, never committed.

**Locks.** `$H` runs a command in one of two machine-wide slots: every `lake build` in `proofs`, `check-axioms`, `check-core`, `check-kernel`, `lc78-lc-check.sh`, `just extract`, `cargo kani`, `lkd-lc-incl-test --budget`. `$E` likewise with two e2e slots. Both scripts:

```bash
#!/bin/bash
# lc78-heavy.sh (lc78-e2e.sh: the same with lc78-e2e-$i.lock)
while :; do for i in 1 2; do
  flock -n -E 75 /projects/leanKohakuDesktop/.tools/lc78-heavy-$i.lock "$@"; r=$?
  [ $r -ne 75 ] && exit $r
done; sleep 30; done
```

**The Lean check for a tree ahead of its Rust** (`lc78-lc-check.sh`, for lc7-wire and lc7-scaffold, whose trees hold WIRE_LEAN without the Rust codecs, so `Refinement.LcWire` and `LcChannel` do not build there): `lake build` of every module under `proofs/LkdProofs/Lc` (none imports a refinement), then a scratch file importing them all with every `#print axioms Lkd.Lc.…` line of `Audit.lean`, except those starting with `$LC_CHECK_SKIP` when set, checked as `check-axioms.sh` checks (no `sorryAx`, one report per line, nothing outside `AXIOMS.allow`); it prints `lc check passed (n theorems)`.

**Disk and memory.** Before copying a target or caches, `df --output=avail -BG /projects` shows at least 60 G, else wait and post. Targets are moved or deleted at the points the integration names; worktrees and branches stay until master. `/tmp` is a 6.3 GB tmpfs: delete your e2e leftovers after each run. lkd-ui's tests run with `--test-threads=1` once master is in (stage B on).

**Checks.** Targeted, once after implementing; only a failing check again after a fix; at most three runs of any check; never the full e2e suite, `check-kernel`, `release-check`, `lean-gate` or `just ci` in a track.

**e2e runs.** `cd $WT/proofs/core && lake build LkdBase:static LkdCore:static LkdLc:static LkdLcDev:static; cd $WT/proofs/tests && lake build lkd-e2e-beacon-gen`; the justfile's e2e `cargo build` line (with `lkd-pinentry` and the probe features); `ln -sfn $CARGO_TARGET_DIR $WT/crates/target`; `cd $WT && LKD_E2E_ONLY=<names> $E crates/target/debug/lkd-e2e $WT/crates/target/debug "$(./scripts/foundry.sh)" $WT > $TMPDIR/e2e.log 2>&1`; pass: one `e2e: <name> passed` per name and no `e2e: FAILED` (before lc8-prep's runner, stage A: `e2e: all scenarios passed`, and each name checked present in `crates/e2e/src/main.rs` first, since the old runner skips unknown names); a failure is rerun alone once before it counts; then `rm $WT/crates/target`.

**Commits.** One per logical part, conventional subjects wrapped at 72, a body saying why; `git -c user.name=nconsigny -c user.email=101647594+nconsigny@users.noreply.github.com commit --no-gpg-sign`; no trailers of any kind; never push. A decision's code, unit tests and e2e steps go in commits whose subject ends `(Dn)`.

**Finish.** Kill only your own processes; remove `crates/target`; post a done line (tip, commits, checks and results, what needs a second reviewer).

**Posted names** in `COORDINATION.md`: `BASE_A`, `BASE_A2…`, `WIRE_LEAN`, `WIRE_LEAN2…`, `WIRE_DONE`, `PROBE`, `ANSWERS`, `BASE_B`, `SCAFFOLD_FIX`, `B1`, `INT`.

### The decision gate

At BASE_A the orchestrator puts D1, D2, D3, D4, D5, D6, D7, D22, D25, D32 and D34 to the user once, with their costs (D4's and D1's from PROBE when posted), and posts the answers as `ANSWERS`. Stage B builds the answers given by its start, the recommendations otherwise. The fast-forward of `feat/light-client` waits for every answer; a no reverts the decision's `(Dn)` commits or swaps the constant named, then reruns the targeted checks of what changed; a no to D5, D25 or D32 starts its follow-up off the integrated tip, and the fast-forward does not wait for it.

**The user's answers (2026-10-27, `ANSWERS`), all as recommended**, posted before the stage-A tracks started, so every track built them and no `(Dn)` commit is reverted or constant swapped:

- **D1** (open decision 3): gated by risk to funds. Deposits and Privacy Pools relayed withdrawals blocked on any cause; Tornado relayed withdrawals blocked on a code mismatch, an acknowledgment when unproved or not pinned; ragequit and direct exits never blocked, an acknowledgment only; a stealth send blocked on a Multicall3 mismatch; a token send and a registration an acknowledgment, the token red.
- **D2** (open decision 4): token proofs for the selected address on an explicit refresh and before a token send's review, at most once an epoch.
- **D3** (open decisions 5 and 19) and **D7** (open decision 22): the persistence rules as written.
- **D4** (open decision 23): yes, G12's block and receipts from public endpoints, by hash, on the transaction's `Broadcast(n)` circuit.
- **D5** (open decision 25), **D25** and **D32**: deferred to LC9's follow-ups, not built: `lc9/ens-facts` (ENS names as facts, type 3, query `0x0e`), `lc9/history` (`History(n)`, key set 6, and `AccountFinal`), `lc9/quorum-pins` (pins and key sets for the ENS and price reads, key-set tags 8 and 9 reserved: until then they stayed on the quorum head, labelled agreed by k of n; one endpoint's head, labelled "on one endpoint's word", since 2026-10-28). Each starts off the integrated tip when the user asks; the fast-forward does not wait for them. LC9 built D25 (lc9-history) and, in the UI in place of `lc9/ens-facts` and `lc9/quorum-pins`, D5's and D32's follow-ups (D44 to D48, lc9-ens); query `0x0e` and key-set tags 8 and 9 stay reserved.
- **D6** (open decision 26): a grid of 50,000 blocks.
- **D22**: token snapshots, yes.
- **D34**: the public caches as plaintext files in `lkd-lc`'s directory, Settings' Public caches row saying what they show at rest.

### As built

#### lc7-wire
Lean only (`lc7/wire`, no cargo): WIRE_LEAN `d2083fd`, then the proofs and this text.

- **`LkdLc.Wire`** (runtime, Init only, no new abort site) holds every name of
  [Frames](#frames): the four queries, the seven answers with `StorageCert` to `CacheStored`, the
  error `notPinned` (`codeOk` 1 to 8), the verdict and refusal constants, `Channel.KeySet`, the
  fetches `elBlock`, `elReceipts`, `elStorage` and the responses `StorageProof` and `BlockBody`.
  Encoders are total; decoders are `check parse bytes`; `decodeQueryB` reads `CacheAppend` as a
  `ByteArray` too; the responses are read by `ByteArray` loops (`parseSizedB`, `parseSlotsB`);
  `Channel.keySetOk` is what `Plan.fetchOk` asks of a key set. The new tags sit in helper parsers
  (`parseQueryLc7`, `parseAnswerLc78`, `parseFetchLc78`): `split` runs out of simp steps on an
  if-chain more than nine deep, so refinements unfold them too.
- **Values, as read** (second reviewer). Each answer's `ok` checks the wire's ranges and the
  rules between its own fields; what depends on the chain's table (`Token`'s keys, `Pin`'s
  implementation and proxy, `Pool`'s words) is left to the handlers (25t) and the UI's re-check.
  Every certificate's header is 1 to 2,048 bytes, `Pin`'s and `Pool`'s too (D15). `Pin`'s
  implementation code hash is zero exactly when its account proof is empty. `CacheChunk`'s item
  sizes copy the allocations' cache table (`Wire.cacheItemSize`) and must stay equal to
  `lkd_verified::cache`'s.
- **Restated** (second reviewer): `parseQuery_short` (a tag neither `0x08` nor `0x0b`, at most 51
  bytes), `queryBytes_short` (not `CacheAppend`, 51), `Channel.fetchLength_le` (75); new
  `Channel.fetchBytes_length_le`.
- **Proved** in `LkdProofs.Lc.Wire` (25o, 25q), no sorry, 113 lines in Audit's `[lc7-wire]`
  block: the new frames' round trips, canonical decoding, injectivity and caps; what decodes is a
  value the layout carries (`decodeAnswer_wf` for every answer, `Channel.decodeFetch_wf`,
  `decodeRequest_wf`, `decodeStorageProof_wf`, `decodeBlockBody_wf`; `Lc.decodeQuery_wf`); the
  responses' `ByteArray` decoders (`Channel.decodeStorageProofB_eq` through `parseSlotsB_fst`,
  `decodeBlockBodyB_eq`, with `decodeStorageProofB_some` and `decodeBlockBodyB_some` for their
  callers); one example per frame (`layout_cacheRead` to `layout_tokenRecord`,
  `Channel.layout_elBlock` to `layout_blockBody`); the answers' bodies as the table writes them
  (`body_token` to `body_tokenRecord`).
- **Forced arms**, in WIRE_LEAN only: `LkdLc.Plan`'s `fetchOk`, `deliver` and `fail` (lc7-scaffold
  keeps or replaces them), `Lc.Plan`'s `fetchOk_wf` and `deliver_bounded`, the LC6 test harness's
  `Server.answer` and `describe`.
- **Checked** on the final tip: `lc78-lc-check.sh` (1252 theorems), `check-core.sh` (LkdLc 692
  modules, 26 abort sites, none new), `lkd-lc-plan-test` (113), `lkd-lc-store-test` (224, 3
  unsupported as before), `lkd-lc-incl-test` (623); the core static build at WIRE_LEAN, the
  runtime unchanged since. `Refinement.LcWire` and `LcChannel`
  do not build in this tree until lc7-wire-rs merges it, which runs the whole build and
  `check-axioms.sh`.
#### lc7-wire-rs
Rust, its refinements and the UI's client (`lc7/wire-rs`), merging WIRE_LEAN `d2083fd` and
WIRE_DONE `1b12bf8` (`lc7/wire`'s tip: the branch contains it).

- **`lkd_verified::lc_wire`** (extracted, Aeneas `74aabd5`, no external function): the queries
  `CacheRead`, `CacheAppend`, `CacheCommit`, `MakeTokenSnapshot` (`0x0a` to `0x0d`); the answers
  `Token`, `Pin`, `Pool`, `Included` (`0x85` to `0x88`, anchor kind 2) and `CacheChunk`,
  `CacheStored`, `TokenRecord` (`0x8b` to `0x8d`), with `SlotProof`, `StorageCert`,
  `TokenAnswer`, `PinAnswer`, `PoolCert`, `PoolAnswer`, `InclusionCert`, `IncludedAnswer`,
  `CacheChunk` and `CacheStored`; `ERR_NOT_PINNED`, `PIN_*`, `INCL_*`, `REFUSED_*`, `MAX_SLOTS`.
  A certificate is plain fields, an absent part empty, never an `Option` of a struct.
  `PinAnswer`'s `implementation` and `impl_code` are Lean's `impl` and `implCode` (`impl` is a
  Rust keyword). The value checks `token_ok`, `pin_ok`, `pool_ok`, `included_ok`, `chunk_ok`
  and `stored_ok` are WIRE_LEAN's `ok`s, rule for rule.
- **`lkd_verified::lc_channel`**: `ElBlock` (`0x13`), `ElReceipts` (`0x14`) and `ElStorage`
  (`0x15`) with `KeySet` (`KEYS_PIN` to `KEYS_HISTORY_FOR`, 1 to 7); `StorageProof` and
  `BlockBody` with their encoders and decoders. `BlockBody` keeps a `too_large` flag where Lean
  has `txs = none`.
- **Refined** in `Refinement.LcWire` and `LcChannel` (25o, 25q; 76 lines in Audit's
  `[lc7-wire-rs]` block, no sorry): every new or changed function computes `LkdLc.Wire`'s
  definition on every input, and the round trips, canonicity and injectivity hold of the Rust
  values. The Rust reads absolute offsets in the whole frame where Lean reads the fields after the
  identity (`f.drop 77`), refuses a ninth slot as it reads where Lean refuses it in its `ok`s
  (`certAt`, `certAt_eq`), refuses a `Pool` frame early on its length and word count where Lean
  reads it whole (`parsePool_facts`), and reads a key set at its offset in the request where
  Lean's `parseKeySet` is given the bytes from there.
- **Kani** (second reviewer): CBMC is capped at 16 GB. With LC7's frames in the decoders, an
  arbitrary-length frame left every length check open and CBMC unrolled every answer's branch,
  so the harnesses are split: `parse_answer_total` takes the short answers at fixed lengths;
  `parse_account_total`, `parse_anchored_total` and the new `parse_included_total` and
  `parse_chunk_total` each call their kind's parser from a fixed header with a length and a short
  tail left arbitrary; `decode_encode_query` keeps the fixed-length queries, with
  `decode_encode_check_snapshot` and `decode_encode_lc7_query` alongside it;
  `parse_request_total` covers every request kind on 90 bytes; `decode_encode_el_storage`,
  `decode_encode_el_body` and `block_body_round_trip` are new. `Token`'s, `Pin`'s, `Pool`'s and
  the storage proof's slot and word loops run at most `MAX_SLOTS` times, yet their harnesses
  exceeded 16 GB with one slot, so their totality is the refinement's. All 27 `lc_wire` and
  `lc_channel` harnesses passed (part 1), and so did the two that reach the functions part 2
  rewrote.
- **`lkd_ui::lc`** (tested, `lc::tests`): `ask_answer`; `ask_within`, which asks again after
  `Pending`, pausing 50 ms to 5 s, and after `WouldBlock` or `TimedOut`, until within;
  `check_identity`, `check_anchor`; `recheck_storage` (`header::verify` under the hash at the
  number, `mpt::account` under its state root, `mpt::storage` per key, equal values) and
  `recheck_included` (the proving header under the anchor's EL hash, N's header under its hash at
  N, and, unless N is the proving number, the history contract's account with its code hash and
  `mpt::storage` of word N mod 8191 giving N's hash); `CacheSession`, one `UnixStream` from the
  first `CacheAppend` to the `CacheCommit`, with `TIMEOUT` for reads and writes, closed when
  dropped (D9); `make_token_snapshot`; `error_words` (8: "not pinned in this release");
  `ANSWER_WITHIN` 55 s (client 55 > core `jobMs` 50 > shell EL 45 > netd 12). The keys and
  pinned values are the caller's arguments (`lkd_verified::pins` is lc7-egress's).
- **netd**: `lc.rs` sends `ElStorage` to `lc_storage::el_storage`, and `ElBlock` and
  `ElReceipts` to `lc_bodies::{el_block, el_receipts}`. Both modules are stubs that answer
  `Denied` and ask no node (tested); lc7-core and lc8-phase2 build them.
- **Forced arms**: none outside `lc_wire`, `lc_channel`, netd's `lc.rs` and the UI's `lc.rs`
  (`lkd-lc`, `lkd-lc-core`, `lkd-e2e`, `lkd-launch` and `lkd-gui` compile unchanged).
- **Restated** (second reviewer): `put_fetch_spec` and `parse_fetch_spec` need room for 128 bytes
  (was 64: an `ElStorage` request is up to 75); `fitsQuery` bounds `CacheAppend`'s items and `fits`
  each new answer's byte strings; `decode_block_body_spec` also says the decoder leaves `txs`
  empty when `too_large`, and `decode_encode_block_body` takes such a body; INVARIANTS 25o and
  25q.
- **Fixed on the way**: part 1's extraction passed `just extract`, which exits 0 even when the
  generated Lean is ill-typed, but did not compile in Lean. Aeneas types a Boolean disjunction
  bound by a `let` as a Prop, so `cache_is_set` is now a conjunction of disequalities and
  `included_ok`'s verdict test is a function of its own, `certified`. Both mean what they meant.
- **Checked** on `0e7b1d5`, whose code is the tip's, each once: the core static build; the whole
  `lake build` (3811 jobs, no sorry); `check-axioms.sh` (4214 theorems); `check-core.sh` (LkdLc 692
  modules, 26 abort sites, none new); `lkd-lc-plan-test` (113), `lkd-lc-store-test` (224, 3
  unsupported as before), `lkd-lc-incl-test` (623); nightly fmt; clippy `-D warnings` on
  `lkd-verified`, `lkd-lc-core`, `lkd-lc`, `lkd-netd`, `lkd-ui`, `lkd-e2e` and `lkd-launch`, all
  targets; `cargo test` on `lkd-verified`, `lkd-netd`, `lkd-ui`, `lkd-lc-core` and `lkd-lc` (703
  passed); Kani `parse_included_total` and `parse_chunk_total`; e2e `lc-own`, `lc-snapshot` and
  `lc-tampered-answer`. The extraction is the one `just extract` produced after the fix.
#### lc7-scaffold
Phase 1 (2026-10-27, `lc7/scaffold`, before WIRE_LEAN):

- `LkdLc.Step` holds `step`, moved from `LkdLc.Lc`; while a light client runs it sends `Token`,
  `Pin` and `Pool` to `Storage.tokenLight`, `pinLight` and `poolLight`, and `Included` to
  `Included.includedLight`, the rest as before (without one they stay LC1's `Unsupported`, so
  25p's `step_endpoint_answers` holds as stated); `LkdLc.Ffi.stepC` runs it. `LkdLc.Storage`
  (`makeTokenSnapshot` too) and `LkdLc.Included` are stubs answering `Unsupported`.
- `LkdLc.PlanCommon` (namespace `Lkd.Lc.Plan`, LC6's names): `Ctx` with `chainId`, `Failure`,
  `maxAttempts`, `attemptByte`, `errorMs`, `jobMs` (50 s; 57 s since the stage-A merge, D13),
  `bodyJobMs` (60 s; then 74 s), `timedOut`, `notSsz`; `Lc.fetchMs := Plan.jobMs`.
  `LkdLc.PlanStorage` (`Read.hash`, `maxReads` 48) and
  `LkdLc.PlanIncl` (`Job.hash`, `Ok`): the fixed signatures over stub bodies (headers: the
  reads' and the job's hashes; waiting: one at a named hash; no candidates; responses and
  failures change nothing). Neither imports `Plan` nor `Lc`.
- `Plan` gains `storage := []` and `incl := none`; `Plan`, `Light` and `State` are built by named
  fields. Candidates in the order read, boot, grid, catch-up, storage, incl, poll. `readCands`
  asks the EL headers the storage reads and the job want (`Plan.headersWanted`) whether or not an
  account is read, from attempt 0 while they have no entry; `deliver` keeps a bound header in a
  new entry when it has none, and `failBlock` counts a failure in one (`Plan.setBlock`, at most
  `maxBlocks`); `want` keeps the headers they want (`wantBlocks`: the account's first, then those
  still wanted, at most 4). Polls wait while an account or a storage read waits, never for G12.
  `candidates` is `@[irreducible]` to the elaborator's unifier, which otherwise evaluates it
  while matching `pump`'s results in proofs (past the heartbeat budget once it grew); every
  theorem about `pump` holds of any list of candidates, and `unfold` still opens it.
- `Lc.anchoredFields` (slot, beacon root, finalized number, age, final, tag of a beacon header),
  used by `anchoredAnswer`, for LC7's and LC8's answers.
- Proofs: the contract in `Lc/Core.lean` (`PlanMoves`, `HandlerMoves`, `StorageAnswer`,
  `InclAnswer`, with `PlanMoves.config`, `.cache`, `.waits`, `.now`, `.chain`, `.light`); every
  theorem from `step_good` to the end of `Lc/Core.lean` moved to `Lc/Step.lean` with its name and
  Audit line, `step_query` restated as the dispatch (`StorageQuery`, `InclQuery`), and each
  answer's source (`step_status`, `step_storage`, `step_incl`); the fixed statements for the stubs
  (`Lc/StorageCore.lean`, `Lc/InclCore.lean`); `PlanStorage.deliver_length`, `fail_length`,
  `PlanIncl.ok_none`, `deliver_ok`, `fail_ok`; `Plan.Bounded` gains `storage` and `incl`,
  `wantBlocks_length`; `Evidence.step_ok`, `Anchored.step_anchored`, `Snapshot.snapshot_answers`
  re-proved through the dispatch, statements unchanged.
- The plumbing test (`plumbingCases`, `LkdTests.Lc6.Plumbing`, 23 checks; `lkd-lc-plan-test`
  136): from the core anchored over anvil's block 1, a storage read at the anchor's EL hash asks
  that header from attempt 0, keeps it bound once delivered and holds polls back; an `Account`
  keeps it; G12's job asks its header and holds no poll back; a header no endpoint serves is
  asked three times, then given up; at most 4 headers held.

Phase 2 (2026-10-27, `lc7/scaffold`, WIRE_LEAN d2083fd merged, then WIRE_DONE 1b12bf8 before the
checks; no WIRE_LEAN2 was posted):

- Both merges were clean: lc7-wire's forced arms (`Plan.fetchOk` for `ElBlock`, `ElReceipts` and
  `ElStorage`, the last with `Wire.Channel.keySetOk`; `fetchOk_wf`; the test harness's) stand
  beside phase 1's header changes, and with WIRE_DONE's proofs every `Lkd.Lc` theorem of
  `Audit.lean` is checked here (`lc78-lc-check.sh` with no `LC_CHECK_SKIP`).
- While a light client runs, `step` sends `MakeTokenSnapshot` to `Storage.makeTokenSnapshot`
  (`StorageQuery`'s fourth case). The cache frames stay with `query`: one that reaches the core is
  answered `Unsupported` and changes nothing, light client or not (`step_cacheFrame`), and the core
  never gives `CacheChunk` or `CacheStored` (`step_no_cache_answer`). `StorageAnswer` and
  `InclAnswer` now name `Token`, `Pin`, `Pool`, `TokenRecord` and `Included`, as the fixed text
  has them; `step_storage` and `step_incl` hold unchanged.
- `deliver` and `fail` hand G12's fetches (`ElBlock`, `ElReceipts`, `ElStorage(…, HistoryFor)`)
  to `PlanIncl.deliver` and `PlanIncl.fail` on `Plan.incl`, and every other `ElStorage` to
  `PlanStorage`'s on `Plan.storage`, with the EL headers bound so far (`Plan.rlpOf`);
  `deliver_bounded` and `fail_bounded` rest only on the parts' `deliver_length`, `fail_length`,
  `deliver_ok` and `fail_ok`.
- D13 in the planner: `Fetch.isBody` (`ElBlock`, `ElReceipts`) and `Fetch.isStorage` (`ElStorage`)
  in `PlanCommon`; `issue` sends a fetch only when `Plan.mayAsk` allows it: a body's only while no
  account or storage read waits at a named EL hash (`Plan.readWaits`, which the polls use too) and
  at most `maxStorageWithBody` (4) storage fetches are in flight, a storage fetch beside a body's
  only while fewer are. `expire` gives a body's fetch `bodyJobMs` and any other `jobMs`
  (`Job.waitMs`), and `fetched` counts a paged fetch's age from its last page (`since` set on each
  page). `issue_ok` and `foldl_issue_asked` read the longer guard; `pump_spec` is unchanged.
- The plumbing test (44 checks; `lkd-lc-plan-test` 157): the stubs ask no body, so `Plan.issue` is
  offered one directly on the anchored run: sent with nothing waiting, held back by a waiting
  storage or account read at the anchor's EL hash, not by one elsewhere, one that ended, or G12's
  own job; sent beside four storage fetches, not five; a storage fetch joins a body's and three
  others, not four, and is not capped with no body in flight; a storage fetch times out past
  50 s and a body's past 60 s, a page restarting the clock.
#### lc7-facts
Built on `lc7/facts` off BASE_A (c26e521).

- **Storage facts (25k).** `LkdLc.Facts.contract` (the code hash of the account `account` reads),
  `storage` (the header `Anchor.bind` keeps, the account by `accountB` under its state root, then
  each slot by `storageB` under the account's storage root, a slot proved absent 0) and
  `storageAt` (the same under a state root given, no header bound), slots as (key, proof nodes);
  `Lc.Facts.contract_spec`, `storage_spec`, `storageAt_spec`, over `values_eq_some`.
  `LkdLc.Facts` imports `LkdLc.Pins`, so that `LkdLc.Lc` sees the table without an import of its
  own.
- **The pin table's lemmas** (`LkdProofs.Lc.Pins`): `word_length` and every derived slot's width
  from it (`pinSlots_width`, `tokenSlots_width`, `headSlots_width`, `rootSlot_width`, `plus`,
  `mappingSlot`, `historySlot`); by `decide` on literal fields only: `pins_wf` (widths, slots,
  masks and expected values below 2²⁵⁶, gates 1 to 15, at most 7 slots a pin), `contracts_nodup`,
  `uses_lt`, `tokens_pin_lt`, `pools_pin_lt`, `tokens_wf`, `token_contracts` (the tokens'
  contracts are `Spec.Tokens`' on every chain, index by index, but for those listed as unpinned,
  `unpinnedTokens`: mainnet's stETH and wstETH, which have no row, `unpinned_tokenOf`), `tokenSlots_table` (a token read asks 1 to 8
  32-byte slots).
- **Fact type 2 (25s).** `LkdLc.Wire.Snapshot.TokenFact {index, owner, contract, account, proof,
  slots : List (Bytes × ByteArray)}` (each slot a 32-byte value and its proof's nodes),
  `Record.tokens := []`, `tokenFixed` 135, `slotFixed` 36, `maxSlots` 8; `parseFacts` reads the
  account facts while the next byte is type 1, at most n, then `parseTokens` the rest, so a type
  1 after a type 2 fails to parse and `check`'s re-encoding refuses any other order; the
  `ByteArray` loops `parseFactsB`, `parseTokensB`, `parseSlotsB`. `LkdLc.Lc.tokenHeld` is the
  held rule and `verdicts chain root facts tokens` gives the account facts' verdicts, then the
  token facts'; `checkRecord` passes `s.config.chainId`; `snapshotRecord` writes `tokens := []`.
  Proofs: `Lc.Wire.Snapshot`'s codec theorems with token facts; `Lc.snapshot_held` now concludes
  that fact k is an account fact `Spec.Mpt.account` proves or a token fact `tokenHeld` keeps,
  `Lc.SnapshotToken`'s `tokenHeld_iff` (the rule is exactly `TokenHolds`), `TokenHolds.balance`
  and `snapshot_token_held`; `record_sound` adds `r.tokens = []`. `snapshot_answers` and the
  imports of `Lc/Snapshot.lean` are untouched (lc7-scaffold's).
- **Rust.** `lkd_verified::snapshot::{TokenFact, TokenSlot}` (plain fields, `Clone` derived),
  `Record.tokens`, `FACT_TOKEN`, `TOKEN_FIXED`, `SLOT_FIXED`, `MAX_SLOTS`; the account facts' loop
  keeps one `u8` state (reading, past them, refused) and `account_at`; one loop a function
  (`parse_tokens`, `parse_slots`, `put_tokens`, `put_slots`). `Refinement.Snapshot` proves them
  (`predictF`, `predictS`, `predict`); the names other blocks of `Audit.lean` list
  (`parseFacts_all`, `parseFactsB_fst`, `predict_none`, `predict_some`) are kept. Kani adds
  `parse_slot_total`; `parse_token` and `parse_slots` have no harness: a vector of slots, each
  of symbolic length, exhausted CBMC's 20 GB even for one slot at a concrete offset and count
  (three runs), as `Vec<Fact>` does, and the refinement proves both total. `lkd_ui::snapshot`:
  `MAKE_WITHIN` 55 s (D13); token facts carried, not shown (`Token`, `Cache::tokens`, their
  verdicts after the account facts'); `split(head, facts, tokens)`; `recheck` refuses a record
  with a token fact (`MakeSnapshot` writes none); `Made::tokens`. `tokens: Vec::new()` at the five
  test literals.
- **The recorded blocks** (`vectors/pins`, `fetch.py`, 2026-10-27): mainnet block 26,280,412
  (`0xc62771e7…6f6426`) from eth.drpc.org (proofs) and rpc.mevblocker.io (oracles), and Sepolia
  block 12,001,519 (`0x5bb6dbed…c47674`) from rpc.sepolia.ethpandaops.io and 0xrpc.io, each six
  behind the first provider's head and its hash given by both. `lkd-lc-pins-test`: 569 checks,
  every key derived as the endpoint echoed it, every pin of both chains matched (USDC's and the
  Entrypoint's implementations included), every token balance `balanceOf`'s (USDC's frozen flag
  on the blacklisted holder `0x80097cdc…a12883` only), every pool root its contract's, the
  Entrypoint's head words `assetConfig(ETH)`'s: the base's mainnet and Sepolia rows needed no fix.
  Sepolia's was recorded again on 2026-10-28 (block 12,012,139, `0xf74057da…ce4d62`, the same two
  providers) when WETH was re-pinned to `0xfff9…6b14`, with holders of that WETH.
  `lkd-lc-plan-test` 118 (5 new: token facts after the account fact, their verdicts after its, a
  type 1 after a type 2 refused). `just lc` runs `lkd-ssz-test`, `lkd-lc-incl-test` (times printed,
  no budget) and `lkd-lc-pins-test` too.
- **For stage B.** lc7-core: a token read's `TokenFact` is
  `⟨index, owner, contract, account, account nodes, keys' values as words with their nodes⟩`; the
  held rule compares each word's number with `storageB`'s value and takes the pin from
  `Pins.pinOf c tok.pin`. lc7-tokens-ui: `make` asks `MakeSnapshot` only and `recheck` refuses
  token facts; `MakeTokenSnapshot`'s records need a recheck of their own.
- Second reviewer (storage): fact type 2, its codec and the held rule (25s).
#### lc7-egress

Built 2026-10-27 on `lc7/egress` (off BASE_A). **The pin table in Rust**: `lkd_verified::pins`,
transcribed from this section's text, every row of every chain (the development chain's 0 to 16
too), with the derivations `pin_count`/`pin`, `token_count`/`token`, `pool_count`/`pool` (by
index), `pin_of`/`pool_of` (the first index whose contract, or whose pin's contract, is an
address), `gates` (a condition's flows, counted from 1 as a verdict's detail), `pin_slots`,
`mapping_slot`, `token_slot`, `token_slots`, `plus`, `head_slots`, `head_value` (when below 2⁶⁴,
which every value a root slot takes is), `root_slot`, `history_slot`, `balance`, `verdict` (with
the upgraded address and the failed condition's place), `verdict_byte`, `detail_byte` and
`keys_of` (egress's key sets). `LkdProofs.Refinement.Pins` refines each against `LkdLc.Pins` on
every input, and proves the tables equal row by row (`mainnet_pins` to `devnet_pools`, by
`decide +kernel` on the literals): the transcription agrees with the base's table, so no
BASE_A2 was needed. The rows name every address and code hash, and the uniform arrays
(`NO_CONDITIONS`, `NO_USES`), as constants: spelled out inline, a row's `[X, X]` is extracted as
an `Array.repeat` let, and `lean -c` of the 49-row table alone took over 40 GB; named, it takes 3
s and 1.5 GB, and `Extraction/Funs.lean` about 4 GB. Rust tests: the four literal keys, the
proxies' standard slots, the tables' coherence (distinct contracts, uses and pool pins in range,
token contracts equal to `tokens`'), each verdict, each key set. **Egress v8 restated (10i)**
and D4's commit, as [Egress v8](#egress-v8-invariant-10i)'s as-built paragraph says;
`Spec.Egress` gains `Keys`, `keysOf`, `keysGroup`, `storageParams`, `storageByHash_pinned`,
`storageByHash_group`, `g12_by_hash`, `g12_public`; `publicGroup_account`, `_broadcast`, `_head`
(and `code_group`) restated for the new request kinds. **netd**: `Node::storage_by_hash`,
`block_by_hash`, `block_receipts`, `Public::number`'s arms, the 8 MiB cap for G12's two,
`Failure::TooLarge` (HTTP and IPC; the channel's `TooLarge`; the beacon class keeps `Node` for an
over-cap body), `lc.rs`'s `code()` arm, `Upstream::header_at` and the `HeaderAt` arm. **netproto**
`HeaderAt` (`0x20`, 9 bytes) and `Header` (`0x94`, 1 to 2,048 bytes). **The UI**:
`Netd::header_at`, `proved::cross_check_block` (D35, `Crossed` public, `CROSSED_KEPT` = 8),
balances' `cross_check` over it (verdicts and labels unchanged), `proved::shared_wait` (D37,
`SHARED_SPREAD` = 6 s; one slot is 1 s on the development chain, else 12 s), noted when the
`Account` answers arrive.

For the tracks that build on it: lc7-core's `lc_storage.rs` maps a `KeySet` to `egress::Keys`
one to one and calls `Node::storage_by_hash(&keys, &hash)` (the request names netd's own chain),
then `reads::storage_part(&v, &read.contract, &read.slots)` with `pins::keys_of(chain, &keys)`;
lc8-phase2's `lc_bodies.rs` calls `block_by_hash(&hN, &tx, true)`, on `Failure::TooLarge`
`block_by_hash(&hN, &tx, false)` (the header alone), and `block_receipts(&hN, &tx)`, mapping
`Failure::TooLarge` through `code()`; the UI tracks call `proved::cross_check_block` before a
token, pin or pool shows green or gates a flow and before `Included` persists a proved outcome,
and wait `proved::shared_wait()` before a pin or pool batch. Second reviewer: 10i (with
`Public::number`'s arms and `HeaderAt`), the netproto request, the cross-check's callers (mixing),
the pin table's data.
#### lc8-prep

**PROBE** (2026-10-27, D4 and D13). One mainnet block of about 1.5 MB of JSON, 26,274,730 (230
transactions; none of the 59 blocks before the finalized head came near it, 63 to 850 KB), and
one recent Sepolia block, 12,001,201 (129 transactions), asked by hash of every suggested
endpoint (`lkd_ctlproto::SUGGESTED`) three times per method, so nine answers a row (nearest-rank
percentiles); HTTP/1.1, netd's `User-Agent`, no compression; over Tor the pinned tor 0.4.9.14
with a SOCKS port of its own, a fresh circuit per endpoint and round:

| Chain, request | JSON bytes | Direct p50 / p95 (s) | Tor p50 / p95 (s) |
|---|---|---|---|
| mainnet, `eth_getBlockByHash(h, true)` | 1,474,373 | 0.16 / 0.41 | 3.18 / 11.84 |
| mainnet, `eth_getBlockByHash(h, false)` | 19,670 | 0.08 / 0.16 | 0.71 / 1.92 |
| mainnet, `eth_getBlockReceipts(h)` | 4,004,659 | 0.32 / 0.72 | 4.45 / **19.80** |
| Sepolia, `eth_getBlockByHash(h, true)` | 231,129 | 0.25 / 0.64 | 1.38 / 1.50 |
| Sepolia, `eth_getBlockByHash(h, false)` | 12,767 | 0.16 / 0.41 | 0.87 / 1.21 |
| Sepolia, `eth_getBlockReceipts(h)` | 331,297 | 0.27 / 0.67 | 1.26 / 2.41 |

One whole pin batch per chain and endpoint over Tor, serially, at a block hash four blocks behind
the head: mainnet 22 `eth_getProof` (20 pins and 2 implementations), 235,807 bytes, in 14.6, 17.8
and 20.0 s; Sepolia 13 (12 and 1), 104,926 bytes, in 17.1, 25.8 and 25.9 s; a proof's p50 / p95
0.70 / 1.25 s on mainnet, 1.88 / 2.25 s on Sepolia; none failed. **The largest body's p95 over
Tor is 19.80 s** (the 4.0 MB receipts; the slowest of nine, the others 11.41 s and below), above
15 s: D13's rule makes `BODY_DEADLINE` ⌈4/3 · 19.80⌉ = 27 s, and the constants derived from it,
at BASE_B. D4's cost on this block: 5.5 MB of JSON, 0.3 to 1.1 s directly and 2.9 to 31.7 s over
Tor (median 7.1 s) for a transaction's block and receipts. OnFinality answers HTTP 429 to back-to-back requests (six
of nine directly, one over Tor, each served on a retry two seconds later), which G12's serialized
history proof, block and receipts meet: `attempt + 1` moves to the next endpoint.

**Built.** `crates/netd/src/envelopes.rs`: a block's transactions and receipts re-encoded as
`fetch.py` does (types 0 to 4, the fields in the execution specification's order), unknown
types and malformed fields refused; its tests hold the two kept blocks' JSON
(`crates/netd/tests/fixtures/inclusion`, recorded with netd's `User-Agent`, SHA256SUMS) to the
vectors' `txs` and `receipts` lines byte for byte. Journal kinds 9 (`Included`, 120 bytes) and
10 (`CacheMark`, 55 bytes), their rules in the codec, with `Spec.JournalLc` and the refinement
(round trips, canonicity; the rows Journal Included records and Journal cache marks); `keyd`
keeps every `Included` record and the newest mark per chain and cache, at most 64 a chain;
kind 8 left to approvals. `lkd-lc-core`'s `request_len` reads `ElStorage`'s key set at offset 34
(the ABI review). The e2e runner: `REST` a slice with the five tracks' markers after
`lc-history`, every scenario through one helper saying `e2e: <name> passed`, unknown names
refused at start, `LKD_E2E_SKIP` and `LKD_E2E_KEEP_GOING`; `lc6.rs`'s `Following` and `Setup`
the crate's (placement before the history, EIP-2935 planted, automine off, a clean ledger) and
the scenario `lc-history`. `lkd_ui::history` needed no new arm: each of its matches over records
ends in a wildcard.
#### lc7-cache

Built on `lc7/cache-store` (25v's store part; 26a restated, its second reviewer pending).

- **`lkd_verified::cache`** (`Spec.Cache`, `Refinement.Cache`, every public function refined,
  53 Audit lines): `regions(chain)`, `item_size`, `kind_of`, `has_root`; the items' codecs
  `encode_`/`decode_` `leaf`, `spent`, `pp_deposit`, `pp_ragequit`, `announced`, `pp_withdrawal`
  (32, 40, 140, 108, 111, 88 bytes; the ASP's leaves are leaves), each decoder reading the fields
  where its encoder writes them and keeping them only when they encode back to the bytes; `Slot`
  with `encode_slot`/`decode_slot`; `choose`; `digest`; `tree_extends(TreeKind::{TornadoMimc,
  LeanImt}, leaves, root)`, Tornado's root built as `wallet::tree_of` builds it (20
  `mimc::level_up`s, the top node, `zeros[20]` for no leaves, none past 2^20 leaves) and Privacy
  Pools' as `pools::sync` does (`leanimt::root`). The item fields check against the decoders:
  `pp_logs::{Deposited, Ragequit, Withdrawn}` (a value below 2^128, 16 bytes), the nullifier hash
  `tornado::decode_withdrawal` reads, and `stealth::Announcement` with the block and transaction
  `scan_stealth` keeps (the amount as a flag and 16 bytes, no `Option` in the struct); no size
  of the table needed a correction.
- **Capacities** (items): Tornado's trees 2^20, their contract's own 20 levels; the LeanIMT trees
  (Privacy Pools' state tree, the association set) 2^20 too, since their depth grows to 32 and
  2^32 leaves of 32 bytes is no file (75 times the PP pool's 13,937 leaves at the survey);
  mainnet's Tornado spent sets 2^19, at least 5.4 times each pool's deposits at the survey
  (75,153, 96,425, 78,767, 49,612: a set never outgrows its deposits); every other set 2^16, at
  least 4.7 times the PP pool's leaves (which bound its deposits, withdrawals and ragequits)
  and 22 times Sepolia's largest pool (2,930 deposits); the announcements, which the survey did
  not count, 2^16 too. The announcements' region has index 0.
- **File sizes**, every region full (sparse: only what was appended is written): mainnet
  314,568,704 bytes (300 MiB: the design's "about 140 MiB" counted the Tornado trees alone),
  Sepolia 115,834,880 (110 MiB), the development chain 168,800,256 (161 MiB). `RLIMIT_FSIZE`
  (`evidence::LIMIT`) is 320 MiB.
- **`lkd_lc::cache`**: `Cache::{open, stored, read, append, commit, discard}`, `layout`,
  `file_size`, `header`, errors `Malformed` (1), `Unsupported` (2), `Refused` (5), `Busy` (6).
  "Order" refuses a commit at a block below the committed one; a set's commit with a nonzero root
  is refused, and a set's slot with one does not load. An append at 0 empties both slots and
  syncs them whatever was committed. A region is loaded with at most two digests, the newer
  slot's first. `main.rs` opens the file in serve mode right after the evidence and hands it to
  `Shell::set_cache`; the frames are lc8-channel's.
- **Tests**: `crates/lc/tests/cache.rs` (9: append, commit and read, also after reopening; roots
  and alternating slots; a crash between items and slot, a slot written half; a tampered item;
  restart; `Busy` and discard; refusals and capacity; the file's lock, links, reset; layout and
  sizes within `RLIMIT_FSIZE`); `tests/sandbox.rs`'s `cache` scenario and the sparse `file-size`
  one; `evidence::tests::writes_stay_in_the_layout`; the verified module's unit tests (round
  trips, slots, `choose`, regions, trees against `mimc::root_of` and `leanimt::root`).
#### lc7-core
Built on `lc7/core` (off BASE_B 0c4a852). **`lkd-lc`** (`LkdLc.PlanStorage`, `LkdLc.Storage`):
storage reads keyed by key set and EL hash, at most 48, the newest first, reads at a hash the
anchor no longer names dropped when another is wanted; asked as `ElStorage` at their attempt once
the EL header there is bound; a response held only when `PlanStorage.check` accepts it
(`Facts.storage` under that header reads exactly the endpoint's account and values, the keys from
`PlanStorage.keysOf`, which mirrors `pins::keys_of`'s LC7 rows); refused or failed, asked again
on the next endpoint, after `maxAttempts` `Refused` or `Unreachable`, told for `errorMs`. A read
made from its hash alone (`{ hash := h }`, the scaffold's plumbing test) has the key set
`History(0)`, which these reads never ask (D25), and waits for its header. The handlers answer
through one `respond` (the answer, else a read's error while told, else `Refused` with the reads
dropped when they hold responses that make no answer, else `Pending`); `MakeTokenSnapshot` leaves
out a token whose fact does not hold. Every answer is checked again and fits lcproto by a check
on its fields and its body's formula (`fitsToken`, `fitsPin`, `fitsPool`, `recordOk`), with
numerals for the widths (no new abort site). **Scaffold fix** (SCAFFOLD_FIX 944b844):
`Plan.failBlock`, giving an EL header up, tells `PlanStorage.fail` and `PlanIncl.fail` as a
failure of `ElHeader(0, h)`, so no read waits for ever on a header no endpoint gives, holding the
polls back; a read wanted again re-asks a header given up more than `errorMs` ago
(`Storage.retryHeader`). **Proofs**: StorageCore's twelve fixed statements for the real handlers;
`PlanStorage`'s bounds and `check_spec`; 25t (`LkdProofs.Lc.Storage`: `token_sound`, `pin_sound`,
`pool_sound`, `tokenRecord_sound`, over `AnchorProved`, `SlotsRead`, `WordsRead`). **netd**
(`lc_storage.rs`): the key set to egress `Keys` one to one, one endpoint by owner (token),
transaction (`HistoryFor`) or contract, read through `reads::storage_part` and `proof_bytes`
(master's `proof_nodes` kept) and `reads::storage_values` (a quantity or a padded word), the
address and keys checked in order, past a page `TooLarge`. **Tests**: `lkd-lc-plan-test`'s LC7
cases (`LkdTests.Lc7`: the fake beacon over the recorded mainnet block `lkd-lc-pins-test` holds,
every pin, holder and pool, a lying or silent storage server, `MakeTokenSnapshot`'s reads at the
finalized header), `lkd-lc-pins-test`'s development-chain keys against `cast`'s, netd's fake-node
tests, e2e `lc-tokens`, `lc-pins`, `lc-pools` (`crates/e2e/src/lc7.rs`) with the liar's storage
mode (`proved::lie_about_storage`). **What anvil does that no chain does**, found by those
scenarios: `anvil_setCode` and `anvil_setStorageAt` change the newest block's state in place,
under a header that names the state before, so every proof at that block is refused, rightly,
until the light client anchors past it (and EIP-2935's slots, set by `Setup::history` before each
block, do so to every block: the scenarios place the history contract's code alone); and a slot
written to zero stays a leaf holding RLP(0), which no Ethereum trie holds and `storageB` refuses
(the development chain's PP pool `dead` flag, a fresh Tornado pool's head): the scenarios give
those slots a value first. Second reviewer: 25t's statements.
#### lc8-phase2
Built on `lc8/phase2` (off BASE_B 0c4a852; [Inclusion, as built, phase 2](#inclusion-as-built-lc8-phase-2)):
`LkdLc.Inclusion` in D36's order through `settle` (25l restated: `verdict_proved`,
`verdict_ahead_iff`, `verdict_tooOld_iff`, `verdict_tooLarge` re-proved, statements kept;
`verdict_notInBlock`, `verdict_eq_settle` new); `LkdLc.PlanIncl`, the job (`Ok`: at most 8
results, the buffers' bounds; `ok_none`, `deliver_ok`, `fail_ok` re-proved, `point_ok` new);
`LkdLc.Included`, the handler (InclCore's three fixed statements re-proved; 25u
`Lc.Included.included_sound`, new after 25l in INVARIANTS); netd's `lc_bodies.rs`; the job cases
and the timed whole job in `lkd-lc-incl-test` (`--budget` fails above 1 s, as `lkd-bls-test`'s
budget); e2e `lc-mined`, and the e2e chain's EIP-2935 slot written by the system address's
transaction in the next block, automine off (`beacon.rs`: anvil's `anvil_setStorageAt` made every
earlier block unprovable). Merged lc7-core's SCAFFOLD_FIX 944b844 (`Plan.failBlock` tells
`PlanIncl.fail` of a header given up). `lc-mined` needs lc7-core's netd `lc_storage.rs` (the
history proof's `ElStorage`): it passed here with lc7-core's 7dfee0a's `lc_storage.rs` and
`reads.rs` laid over uncommitted, and runs at B1 on the merge. Second reviewer: 25l's statement
with D36's order and 25u's (spec review); netd's `lc_bodies.rs` reads untrusted JSON only through
`header_rlp` and `envelopes`.
#### lc8-channel

Built on `lc8/channel` off BASE_B: the shell's cache frames (D9; 25r's cache-frame clause, 25v's
shell clause), netd's held responses (D12), the deadlines over PROBE's 27 s body deadline (D13).

- **The cache frames** (`crates/lc/src/shell.rs`): a whole client frame tagged `0x0a` to `0x0c`
  is decoded with `lc_wire::decode_query` and answered by the shell, never handed to the core:
  from the caches' file through `Cache::answer` (`crates/lc/src/cache.rs`, the glue: `read` with
  `MAX_CHUNK` = 65,413 bytes, `append`, `commit`, their results as `CacheChunk` and
  `CacheStored`, a refusal as its code), `Unsupported` without a file, `Malformed` when it does
  not decode. The identity is the core's `Status` answer, asked once at start (`Shell::load`,
  serving shells only) on connection id `u32::MAX`, which `fresh_id` never gives a client; that
  answer reaches no client. `Shell::close`, the one path every closed connection takes (its end,
  an error, a length out of bounds, `IDLE`), calls `Cache::discard(conn)` before the core hears
  `Closed(conn)`. A cache frame is read and answered as any other frame: its connection is not
  read again until the answer is written.
- **The deadlines** (D13): netd's `EL_DEADLINE` 12 s, `BODY_DEADLINE` 27 s (`ElBlock`,
  `ElReceipts`), `BEACON_DEADLINE` 8 s, `LONGEST_DEADLINE` = `BODY_DEADLINE`; the shell's
  `BEACON_FETCH_DEADLINE` 48 s, `EL_FETCH_DEADLINE` 52 s and `BODY_FETCH_DEADLINE` 67 s, each
  `AHEAD` (10 + 27 s) + netd's + `MARGIN` (3 s), picked by `fetch_deadline(request)` from the
  request's kind, and `PAGE_DEADLINE` 40 s for a `FetchPage`, which the design's list did not
  name: netd answers a page from what it holds, so its own share is nothing, and every page stays
  below the core's deadlines, which count a paged fetch from its last page; the UI's netd
  `TIMEOUT` 10 + 27 + 3 = 40 s and `lc::ANSWER_WITHIN` 62 s (BASE_B moved it from 55 s).
- **Held responses** (`crates/netd/src/lc.rs`): by (generation, tag), only responses longer than
  `MAX_PAGE`, at most `MAX_HELD` = 4 of at most `MAX_HELD_BYTES` = 24 MiB together, ordered by a
  count of the pages served; one more evicts the least recently paged first; a fetch under a
  (generation, tag) held drops it, whatever the fetch's outcome; a response is dropped once its
  last page is served, which D12 did not say: `lkd-lc`'s planner never asks a page again (a page
  that fails fails its job, which fetches again under a new tag), so a response pulled to its end
  would only take a body's place. `FetchPage` for anything else is `NoPage`, changing nothing.
  `Channel::held` reports the count and bytes held.
- **Answers kept** (`crates/netd/src/lc.rs`, `Recent`, 2026-10-28): the last `MAX_RECENT` = 64
  answers to `ElHeader`, `ElProof` and `ElStorage`, keyed by the fetch with its attempt left
  out, kept for netd's life. The same read at the attempt that fetched it or an earlier one is
  answered from it, asking nothing; a later attempt, which `lkd-lc` sends only after a refusal, a
  timeout or an answer it rejected, drops it and fetches anew. A read by block hash cannot change
  and `lkd-lc` checks every answer, kept or not, so keeping one decides nothing: it only spares
  the endpoints, and Tor's circuits, the same question. A user's Sepolia session asked one
  `HistoryFor` proof 18 times and each pool's root 3 times at one block. Failures are not kept.
- **Tests**: `crates/lc/tests/shell.rs`: cache frames over a socket (2,000 spent-set items in two
  appends, read back in two answers from any start, each naming the core's identity, the core
  answering as before), the refusals with lcproto's codes, no caches' file, `Busy` across live
  connections, a closed and an idle connection's staging dropped, a restart reading what was
  committed, the deadlines by kind; `tests/sandbox.rs`: `cache-frames` (the shell, sandboxed as
  the binary is, answers an append, a commit and a read) and `cache-restart` (a second sandboxed
  process over the same directory reads what the first committed); `lkd-netd`'s `lc::tests`: one
  page not held, a body of six pages pulled across five interleaved one-page fetches, the
  eviction order, the 24 MiB cap, a fetch under a held tag replacing it, malformed datagrams
  leaving what is held; `tests/lc.rs` restated: a one-page `ProvedAccount` leaves nothing to
  page.
#### lc7-tokens-ui
Part 1 (2026-10-27, `lc7/pins-tokens-ui` off BASE_B `0c4a852`, before B1): the UI's logic against
the frames in BASE_B, unit-tested from constructed answers; `lkd-lc` still answers `Pin`, `Token`
and `MakeTokenSnapshot` `Unsupported` until B1's handlers, so no proof is shown green yet.

- **`lkd_ui::pins`** (D1, D21, D28, D35, D37). `prove`: the chain's whole set, `Pin(i)` for every
  pin at once (`ask_all`: each asked, those `Pending` asked again), after `proved::shared_wait`
  (looked at again until it is zero), within `PIN_BATCH_WITHIN` = 67 s (D13's 60 s moved with
  PROBE's 27 s body deadline); `lkd-lc`'s status first, a phase that anchors nothing leaving
  every pin unproved with its words. `check_pin`: `check_identity`, `check_anchor`, index and
  contract the table's, `recheck_storage` at `pins::pin_slots`, the code hash, the
  implementation the proxy slot holds and, when it is the pinned one, its account under the same
  state root, the verdict and detail recomputed (`pins::verdict`); `settle`: a matched pin gates
  only once `cross_check_block` agrees, any other verdict stands (failing safe), a disagreement at
  or below the finalized block is red. Error 8 is "not pinned in this release". `needs(flow)` from
  the table (uses included; the Privacy Pools Entrypoint and pool found by their layouts); `act`
  is D1's table, one function, flow × cause → pass, `W` or block (`Wait` while a batch that could
  block is out); `gate_over` words the lines and the reason. `due`: at start once, before every
  review, explicit or a screen showing pins at most once an epoch (384 s; 8 s on the development
  chain), never automatic. `configured`: the settings' checkpoint and beacon source; without the
  settings (a command typed in another terminal), no `lkd-lc` socket or a zero checkpoint is none
  (`lc_runs`), one that does not answer leaves every pin unproved. Names per chain and index
  (`name`), checked against the tokens' symbols.
- **`lkd_ui::token_proofs`** (D2, D17, D23, D37). `prove`: `Token(i, owner)` for every pinned
  token on `Account(owner)`, within `lc::ANSWER_WITHIN`, each round of asks noted as a refresh's
  `Account` answers are (`proved::note_accounts`), so that no pin or pool read goes out at the
  anchor the token reads use (`lkd-lc` holds it while they wait); `check_token` (the keys `pins::token_slots`, the
  pin byte recomputed with the implementation's code not read); `settle` (a proxy's
  implementation code from the session's pin set, `ImplMismatch` when another, unproved when the
  set has none; the masked balance and the frozen flag; the cross-check). `PROVE_BEFORE_REVIEW` is
  D2's one constant. `overlay` puts a proof younger than an epoch in place of `aggregate3`'s
  value (only where its pin matched); `label` says how a value is known; `gate` is a token
  send's (`W` for any cause); `proved_since` drives D22.
- **Wired.** `wallet::token_balances` overlays proofs; `plan_sending` asks the batch first when
  due (D2: before a token send's review), so its balance check and the review's gate read it;
  `wallet::flow_of`. The TUI (`tui.rs`): `pins_due` before each draw (the review's own batch,
  keyed by its digest and opening time; the session's first once an account was anchored;
  Settings' Networks page), explicit refreshes (`r`: pins and tokens) and another address selected
  (tokens) after their answers (so the shared wait counts from them), Tokens read again (tokens);
  `pin_gate`, `pin_hold`, `warned` (pins' `W`), `answer` (no answer while held), the review's and
  the withdrawals' `Contracts` lines and footers; overview token lines; Tokens' labels; cached
  token values. Ragequit is gated at its signing review, not its proof's. The window
  (`scene_of.rs`): the lead, Sign and send off with the reason as an alert, Home's proved token
  lines. The CLI (`main.rs`): `pin_gate`, `gated`, `confirm_pins` in `send` (stealth), `send
  --token`, `stealth register`, `shield`, `unshield`, `pp deposit`, `pp withdraw`, `pp ragequit`;
  `balance` asks the token batch and labels each token line. Settings' Pins row
  (`light::proof_rows`, `pins::row`). `lkd doctor` (`crates/launch/src/doctor.rs`,
  `proof_window`): on a route through your own node with a light client, "set
  --rpc.eth-proof-window to at least 256 for a reth node".
- **D22** (`snapshot.rs`): `make` asks `MakeTokenSnapshot` for `tokens_of`, the address in use
  whose tokens a batch proved since the last snapshot; `recheck_tokens` (its account fact as
  `recheck`, its token facts' indices pinned tokens in strictly increasing order, a token
  `lkd-lc` left out, red at that block, leaving the rest good, each held: contract, account
  under the header's state root, its code the pin's, the derived keys' values, the verdict
  matched);
  `token_text` shows them at start. `MAKE_WITHIN` = 62 s (D13's numbers).
- **e2e text** changed with the labels: `prices`'s `lkd balance` token lines now end "(the node's
  word: no light client)".
- **Second reviewer (mixing).** D1's table and every gate site (25w); `cross_check_block`'s
  callers in `pins::prove` and `token_proofs::prove`; the CLI without settings judging "configured"
  from `lkd-lc`'s socket (a stale socket, `lkd-lc` crashed, fails closed; no socket at all is no
  light client).
- **For part 2.** Merge B1; `lc-tokens-ui` in `lc7ui.rs`; no direct Tornado withdrawal exists in
  the wallet (every unshield is relayed), so the scenario's direct exit is ragequit.

Part 2 (2026-10-27, B1 `4d85d4a` merged): `lkd-lc` answers `Pin`, `Token` and
`MakeTokenSnapshot`, and the UI runs against it end to end.

- **Merge.** `git merge --no-ff build/lc78-b1`: clean but for `spec/INVARIANTS.md`, merged row by
  row (`rowmerge.py`): 25w beside lc8-channel's 25r and 25v clauses, no row changed by both.
- **`lc-tokens-ui`** (`crates/e2e/src/lc7ui.rs`, in the runner's `[lc7-tokens-ui]` markers), on a
  chain following the fake beacon with `lc7::place_all`'s contracts; its beacon endpoint public
  (behind the fake tor and the TLS proxy, so that netd trusts the test CA the mock ASP and
  relayer use), anvil's words (notes come from recovery words), nonce records of its own, and
  automine off (`Setup::no_mining`: what is sent is mined with the chain's next block, at a slot
  of its own; anvil mining a transaction at once can give its block the newest block's second, a
  slot the beacon chain already has, and the chain then stops there).
  - **D2.** After `r`, the overview's `Token` lines for anvil #0's 2500 USDC, 100 WETH and 40 LINK,
    "(proved at block N, signed by 32 of 32 of the sync committee; final up to F)"; `lkd balance`'s
    WETH line the same; the window's Home, by asset, "This address: 100 WETH (proved at block N,
    …)" once its own `r` asked its batch.
  - **D1.** Each change is answered by `lkd-lc` at an anchor past it before a review opens (anvil
    writes `anvil_setCode` and `anvil_setStorageAt` into the newest block's state in place); a
    code is replaced by its own with a byte after it, which runs as before under a hash nobody
    pinned. WETH's: a 1 WETH transfer's review in the terminal UI says "Contracts     WETH: its
    code is not the code this release reviewed (block N)" and "[W] sign and send anyway", and `W`
    sends it. Tornado's 0.1 ETH pool's: its deposit's review says "Blocked       the code of
    Tornado's 0.1 ETH pool is not the code this release reviewed: nothing can be signed", and `y`
    signs nothing. Privacy Pools from the command line (`lkd-ui`: the launcher forwards no `pp`
    command), the mock ASP and relayer reachable and the wallet started again with `asp` and
    `pp_relayers`: 1 ETH deposited as note 0 with every pin as reviewed, then approved; the
    Entrypoint's EIP-1967 slot naming a copy of its implementation at another address (it runs as
    before): `pp withdraw` exits 2 with "Blocked       the Privacy Pools Entrypoint was upgraded
    after this release (implementation 0x…, seen at block N): nothing can be signed" and the
    ragequit line, the relayer having quoted and been asked to relay nothing; the pool wound down
    by the Entrypoint's owner (`windDownPool`: condition 1, which gates deposits alone, fails): `pp
    ragequit` asks "Not checked as this release reviewed: storage condition 1 of Privacy Pools' ETH
    pool does not hold at block N. Type anyway to go on:", `anyway` is typed, and the deposit
    comes back.
  - The direct exit is ragequit. It needs only the Privacy Pools pool and its uses (`needs`), so an
    Entrypoint upgrade alone leaves it passing with `y`; its `W` here comes from the pool wound
    down.
- **Runs.** The regressions `tokens`, `proved-balances`, `lc-snapshot`, `cli`, `gui` passed on
  their first run after the merge. `lc-tokens-ui` passed on its third: the first stopped at `lkd
  pp` (the launcher's usage), the second at the anchor stalled after two transactions anvil mined
  at once (hence `no_mining`).
- **Checks** on the merged tree, once each: nightly `fmt --check`; `cargo clippy -p lkd-ui -p
  lkd-gui -p lkd-e2e -p lkd-launch --all-targets -- -D warnings`; `cargo test -p lkd-gui -p
  lkd-launch` (38 and 33); `cargo test -p lkd-ui -- --test-threads=1` (149 and 2).
#### lc7-pools-ui

Part 1 (off BASE_B 0c4a852; the UI against BASE_B's frames, before B1's handlers):

- **`lkd_ui::pool_proofs`** (G16): `prove` and `checks` ask `Pool(i)` for every pool a sync
  needs at once, after `proved::shared_wait()` (looked at again until it is zero), within
  `POOL_WITHIN` (`lc::ANSWER_WITHIN`),
  re-check each (`check`: identity, anchor, index, `recheck_storage` at `head_slots` then
  `root_slot(head_value)` under the pinned contract, the Entrypoint naming the pinned pool),
  cross-check its block once per (number, hash) (`cross_check_block`, now
  `proved::CrossChecks`, which pins and tokens use too), and read the words
  (`Head`: Tornado's root and `nextIndex`, the pool's root and size, the Entrypoint's root and
  `assetConfig`). `Rooted` says how a tree was checked: `Proved(Proof)` or `Word(why)`, its
  `text()` the reviews' wording.
- **`lkd_ui::cache`** (G19, D6, D8, D9): the regions this process holds (`Held`), loaded from
  `lkd-lc` (`read_all`, paged) and checked against the newest mark (`note_marks`, `load`);
  `delta_start` on the grid (`GRID` 50,000, `GRID_DEV` 32); `merge_leaves` (by index),
  `merge_set` (by block), `closed_cells`, `confirm` (the two-fetch rule), `pp_cross_check`;
  the syncs `tornado`, `privacy_pool`, `association_set`, `announcements`; commits
  (`commit_due`, `at_exit`, `transfer` over one `CacheSession`, `committed`, the mark kept by
  `keyd`); `rescan`; `summary` and `said` for Settings and the command line.
- **The flows**: `wallet::sync_pools` (and `sync_pool`) for Tornado, `pools::sync`,
  `asp_set(s)` and `config(s)` for Privacy Pools, `privacy::unshield_plan` (the proved root in
  place of `isKnownRoot`), the stealth scan from the cached announcements
  (`wallet::scan_stealth(netd, keyd, chain, (from, to), progress)`), Home's private totals
  (`tui::private_totals`: each tree checked against its proved root), the TUI's jobs noting the
  marks on the connection they hold (`with_keyd`, `ragequit_terms`, `private_totals`), commits
  after each job and at exit, and every `lkd` command committing as it ends and printing what
  the caches found to say. Without a light client every flow reads as before (D23).
- **Deposit times**: `PoolState::before` and `NoteEntry::before` bound a cached leaf's time;
  `privacy::age_of` and `deposited` say it; the guards warn when it is not known.
- **Settings**: the Public caches row after Evidence, D34's note, and the rescan (`R`, the
  window's button; `Job::Rescan` through `asked_keyd`).
- **D6** (the grid, 50,000 blocks; 32 on the development chain): `cache::GRID`, `GRID_DEV`,
  `grid`, `delta_start`, in the commit whose subject ends (D6).
- **Tests** (`lkd-ui`): the re-check and its refusals from a constructed answer, the words of
  each layout, the root lines; paging (a commit landing mid-read restarts it), marks (matched,
  items past the mark, a tampered digest, none, fewer, a rescan's), a tree's stored root, the
  grid and cells, leaves by index, sets by block, the two-fetch rule, final-only runs, the
  Privacy Pools cross-check with recomputed commitments, a session's appends then commit, a
  refused append, the newest mark per cache; Settings' row.

Part 2 (B1 4d85d4a merged; INVARIANTS 25v keeps the shell's clause and the UI's):

- **e2e** (`crates/e2e/src/lc7pools.rs`, in the runner's `[lc7-pools-ui]` block). Each scenario
  follows a chain of its own (`lc6::following`): every pin placed as `lc-pins` places it, someone
  else's deposits in each pool (anvil keeps a slot written to zero as a leaf no trie holds, which
  the light client rightly refuses: a fresh Tornado pool's head, and the depth Privacy Pools'
  tree writes at its first insertion), the wallet on anvil's words with a ledger of its own. The
  commands run `lkd-ui` in a runtime directory of their own (`Stack`): netd reaching the relayers
  and the association set provider behind TLS and a fake tor, and the chain through `Node`, a
  proxy that keeps every `eth_getLogs` and can empty one answer; the wallet's `keyd` and `lkd-lc`
  linked in, so that the marks and the cache file are the wallet's.
  - `lc-pools-ui`: 0.1 ETH shielded, the shield's and `lkd shielded`'s crowd lines "(its
    deposits proved at block N; its withdrawals are the endpoints' word)"; the note withdrawn
    through the relayer, "Root 0x… (the pool knows it: proved at block N)" equal to
    `getLastRoot()` at N; 0.5 ETH into Privacy Pools, approved, 0.2 ETH withdrawn, "State root
    0x… (the pool's, proved at block N)" and "ASP root 0x… (the Entrypoint's, proved at block N)"
    equal to `currentRoot()` and `latestRoot()` at their blocks.
  - `lc-cache`: a note shielded and withdrawn. Once the withdrawal's cell is final, a sync whose
    second fetch of it lacks the withdrawal says "two fetches of blocks A to B disagree; neither
    is kept", and the spent set `lkd-lc` holds committed (`CacheRead`) stops short of A; the next
    sync commits it. The wallet started again (D6), every `eth_getLogs` of a pinned pool starts
    past deployment on the 32-block grid, at or after its region's mark's cell. A leaf changed in
    the cache file: "did not match the mark this wallet wrote: synced from deployment"; a home
    whose journal holds no mark: "has no mark in this wallet's journal: synced from deployment";
    each fetches from block 0 again and lists the same notes.
- **A fix the scenarios found**: the withdrawal reviews' root lines and the relayer's transaction
  line printed `0x0x…` (`wallet::hex` writes the `0x`); now once.
- **Checks**: nightly fmt; `cargo clippy -p lkd-ui -p lkd-e2e --all-targets -D warnings`;
  `cargo test -p lkd-ui` serially (151 + 2); e2e `shield`, `privacy-pools`, `stealth` passed;
  `lc-pools-ui` on its second run, after the Privacy Pools placement above; `lc-cache` passed,
  failed once (its withdrawal began before the light client anchored the deposit, so the proved
  tree lacked the note: it now waits), then passed.
#### lc8-ui

Built on `lc8/ui` (off BASE_B 0c4a852): part 1 the UI against BASE_B's frames; part 2 B1's
handlers merged and the scenarios `lc-mined-ui`, `lc-netd-busy` and `lc-killed-mid-body`.

- **`lkd_ui::included`**: G12's asks and D3's and D7's rules. `next` picks one ask a refresh
  from the history: `Included(h, N, 0)` for a `Mined` record without a terminal record, the one
  asked longest ago first (never asked first, then the newest), skipping a refused one until its
  backoff passes (`BACKOFF` 60 s, doubled, up to `BACKOFF_MOST` 1 h) and a too large one left for
  the next session; else D7's check, for a transaction of the account in use that G11's proved
  nonce shows settled at a head, once the anchor's finalized block reaches that head. `run`, on
  the TUI's thread of its own (`App::ask_included`, one at a time, at a refresh's end): the ask
  within `INCLUDED_WITHIN` (15 s), `judge` (identity, transaction and block, anchor,
  `recheck_included` under `pins::HISTORY` and its pinned code hash), the head cross-check of a
  final proving header, `decide` (D3), and `keyd`'s `Remember` of what it allows. `ranked` and
  `shown` are D3's ranking; `consumed` is D7's check of `MakeSnapshot`'s record
  (`snapshot::recheck`, nonce past `n`; since LC9 of the sender's account at F,
  `proved::final_account`, D40); `mined_text` and `level` the words and colours above.
  The index hint is 0: netd's receipts carry no index, and `lkd-lc` looks the hash up.
- **D3 as built**: a proof is kept only at the finalized header, re-checked and cross-checked
  (`proved::cross_check_block` agreeing; another block there is a verifier disagreement, noted
  for the overview's red line; no answer leaves it shown and asked again). Too large is kept, like
  a proof, only from the finalized header and cross-checked, a stricter rule than the decision's
  text (a record naming hN rests on a final header), with your own node (IPC, loopback, onion,
  hybrid: `el_endpoint` uses it) or two or more public endpoints; with one, it is shown and not
  asked again until the next session. Too old is weighed against `Sent.time` with mainnet's and
  Sepolia's slot times (`light::slot_time`): on the development chain it is never plausible.
  Nothing is kept for a hash without a `Sent` record (`lkd status` of another's transaction). A
  record under another checkpoint than the light client's now (the configured one, else the one
  `lkd-lc` was seen running from) is shown "proved under an earlier checkpoint"; after a ceremony
  (`checkpoint_from` typed or `agreed:k/n`) with N within 8191 blocks of the anchor it is asked
  once more a session, and only a proof is kept then; a refusal then shows red over it, anything
  else leaves the earlier proof shown.
- **D7 as built**: `Status::SettledByNonce` comes after a receipt for the hash or a replacement
  at its nonce, before G11's settled; its receipt is still asked for (`Book::unsettled`), so that
  a receipt coming later reopens G12, and a proof then supersedes it. **Restated by LC9 (D40,
  [lc9-ui-b](#lc9-ui-b))**: outcome 1 rests on the sender's account at F, `proved::final_account`
  (an `AccountFinal` answer accepted anchored and final at F, F cross-checked agreeing), through
  `inclusion_keep::settled_keep` with the real acceptance and cross-check: never from an
  unchecked or disagreeing F; `MakeSnapshot` is no longer asked for it.
- **D4**: `included::public_refused` asks `egress::allowed` for `BlockByHash` at a public
  endpoint; with D4's commit it is allowed, and a revert of it makes the UI say "inclusion not
  checked on public endpoints (your choice)" without asking.
- **`lkd_ui::history`**: `Status::Mined` carries the inclusion; `Book::inclusion` ranks the
  records with the session's; the JSON keeps `"status":"mined"` (or `failed`) and adds
  `"inclusion"` (`unproved`, `seen`, `proved`, `proved_not_final`, `proved_earlier_checkpoint`,
  `too_old`, `mislocated`, `too_large`, `not_checked`, `refused`, `disagreement`,
  `settled_by_nonce`) and `"tx_index"`; `status_level` colours it, `styled_lines` lets the History
  screen colour the status alone (a line in one colour would be an alert in the window).
- **The TUI and the window**: the tracked transaction's status and its screen's line under the
  receipt (`inclusion_line`), the History screen's statuses; the window's transaction title
  ("Receipt refused" for a refusal), its Status field in the inclusion's level, and
  `status_color` in `lkd-gui` (red failures, refusals and disagreements; amber the node's word,
  not yet proved, not provable and still waiting, before green, so that "broadcast, not mined
  yet" is amber now), for a status the screen gives no level: a mined transaction's row carries
  `history::status_level`'s (`scene::Row::status`, the tracked one's `included::level`), so
  "succeeded (proved); the node's receipt says it failed" is green there as in the terminal.
- **The command line**: `lkd status <hash>` prints "Inclusion     …" after the receipt: a record
  kept settles it, else one ask, what D3 allows kept when the wallet sent it; exit 0 or 5 by the
  proved status (else the receipt's), 3 not mined, **7** when the light client refused the
  receipt. `send`, `resume`, `speed-up` and `cancel` ask once after the receipt and print the
  line, keeping nothing (no answer is final then), their exit codes the receipt's. Where the
  settings `lkd` passed configure no light client nothing is asked; without settings, only where
  `lkd-lc` runs from a checkpoint.
- **Part 2** (on B1 4d85d4a, merged without a conflict: B1 changes the UI only in `netd.rs`'s
  `TIMEOUT` and `lc.rs`'s `ANSWER_WITHIN`). The command line weighs a kept proof as the TUI
  does: `lkd status <hash>` and `lkd history`, typed in another terminal (no settings), ask
  `lkd-lc`'s `Status` for the checkpoint it runs from (`light_checkpoint` in `main.rs`), so a
  proof kept under another checkpoint says "proved under an earlier checkpoint" there too; part 1
  read only the settings, so the command line said "(proved)".
- **The scenarios** (`crates/e2e/src/lc8ui.rs`, on `lc6::following` chains with EIP-2935's
  history planted, automine off and a nonce ledger of its own): a transaction the scenario waits
  on is mined in a block of its own while the chain is held (`mine_held`: one block at the
  current second, the beacon chain generated over it and served), so the light client's head is
  that block, which no finalized block reaches (a block's state names an older checkpoint), until
  the chain moves again: "(proved, not final)" is a state the scenario holds, not a race with the
  next epoch. `lc-netd-busy` and `lc-killed-mid-body` start the wallet again behind a `Gate` of
  their own (a proxy in front of anvil, a thread a connection, `cast` still reaching anvil
  itself) that holds the first request naming given words, for a time or until let go.
  - `lc-mined-ui` (D3, D7): a transfer from the TUI, driven only by its refresh (`r`): "mined in
    block N (the node's word)" first, yellow; "Nonce 0: mined in block N at index i, succeeded
    (proved, not final)", green, and nothing kept (`lkd history --json`: `"inclusion":"unproved"`);
    the chain moving again, "(proved)", kept: `lkd status <hash>` exits 0 with "Inclusion
    mined in block N at index i, succeeded (proved)", and says so within a few seconds with
    `lkd-lc` stopped (the journal's record: `lkd-lc` answers nothing, and an ask ends in the node's
    word);
    `lkd history --json` says `"status":"mined"`, `"inclusion":"proved"`, `"tx_index":i`. Then
    a transfer from the TUI replaced at its nonce by `cast` (anvil's #0's key, dearer) while the
    chain is held, the replacement mined: the History screen says it is settled by nonce, then
    "settled by nonce at finalized block F, inclusion unproved", yellow, with F at or past the
    replacement's block, and `lkd history --json` `"status":"settled"`,
    `"inclusion":"settled_by_nonce"`. `lkd history` runs as `lkd-ui`: `lkd` passes on only the
    commands its list names (`status`, `balance`, not `history`).
  - `lc-netd-busy` (D13): G12's `eth_getBlockReceipts` held 15 s at the node; meanwhile a
    broadcast (a transfer `cast mktx` signed for anvil's #1) and a receipt poll through
    `lkd_ui::netd::Netd`: each answered after the receipts came back, and within the UI's netd
    timeout, which the scenario derives from `lkd_netd::rpc::TIMEOUT` and
    `lkd_netd::lc::LONGEST_DEADLINE` (40 s with B1's numbers; the design's 33 s was before PROBE
    moved `BODY_DEADLINE`); G12 then proves the transfer.
  - `lc-killed-mid-body` (D12): 200,000 zero bytes of calldata beside the wallet's transfer, one
    block of four pages and more (`eth_sendTransaction`, anvil signing for its account #1: `cast`
    would pass the data as one argument, past the kernel's 128 KiB); the gate holds G12's
    `eth_getBlockByHash(h, true)` until `lkd-lc` is stopped (`SIGSTOP`), then lets it go: netd
    holds the block for its pages, the first waiting in the channel; `lkd balance` and `lkd
    status <hash>` answer within the timeout, the inclusion the node's word (`lkd-lc` does not
    answer its `Status`); continued, `lkd-lc` pages the block netd held, the node asked for it
    once, and G12 proves the transfer.
  - spec/16's Testing passage still gives the design's first numbers for the last two (a 12 s
    receipts fetch, 25 s): for the integration's docs pass.
- Tests: `included::tests` (proved and final kept under R1; R2 after a refresh shows it earlier
  and asks nothing, once more after a ceremony; a too old answer then keeps nothing and the proof
  still shows; settled by nonce reopened by a receipt; too large with one public endpoint not
  kept; too old plausibility; the answer checks; backoff and order; D7 asked once final and its
  record checked; the ranking; words and colours), `history::tests::inclusion_in_lines_and_json`,
  `tui::tests::a_mined_transaction_shows_its_inclusion`, `lkd-gui`'s
  `statuses_colored_by_what_proves_them`, `main.rs`'s exit codes; e2e `lc-mined-ui`,
  `lc-netd-busy`, `lc-killed-mid-body`, and the scenarios that read what part 1 changed
  (`history`, `settled-nonce`, `foreign-nonce`, `cli`, `gui`), passing.
- Second reviewer (storage): the persistence rules in `lkd_ui::included` (`decide`,
  `settled_record`, `consumed`, `next`'s terminal tests) and INVARIANTS' Journal `Included`
  records UI clause.

## LC9: the design as decided

**Decided 2026-10-27; built and integrated 2026-10-27 on `build/lc9-integrate`** ([As built
(LC9)](#as-built-lc9)). The user chose LC9 after LC7 and LC8 landed on `feat/light-client` (6ba32fa; tip 3b0ea9a, the wallet script), asked for parallel agents, for checks and e2e runs that never loop, and to leave `lean-gate` aside for now. Six tracks build from this section in one stage off one base (`build/lc9-base`); where the sections above differed ([What this section overrides](#what-this-section-overrides-lc9)), this section ruled until the integration folded it in, which it has: the sections above say what was built. A track never picks a tag, kind, code, row, name, constant or index this section does not give, and never edits another track's files or functions ([Tracks and what they own](#tracks-and-what-they-own-lc9)). **D4's fallback, accepted by the user on 2026-10-27:** after a restart, G12's reads go to `endpoint_for(tx)` when the broadcast's endpoints are unknown; that endpoint learns that some wallet cares about that block. The code (`Upstream::g12_endpoint`) also falls back within a session once every endpoint that took the broadcast refused or timed out, which the user accepted too (D59, yes). Two review rounds shaped this section: G9's reorg check rides the shared reads' circuit and timing, never the head's (D38, D39); a name not proved at the anchor asks `W` before a send (D44, D46); the UI's re-checks take what was asked and state every value shown (D49); D7's outcome 1 rests on `AccountFinal`, cross-checked (D40); D1 fails closed where `lkd` passed no settings (D60); the live run says which binaries this host can run (D52).

### Scope (LC9)

| Built | Not in LC9 |
|---|---|
| `AccountFinal` at the finalized header (D25, D40): G11's "settled at block F, final" and D7's outcome 1 | The received-funds notice (D55) |
| G9's reorg check for the blocks a shown pin or pool batch was proved at (D38, D39): `BlockHash(n, final)` read with key set 6 `History(n)`, now issued, on `Shared` (moved from `Head`), routed by the proving header's hash; the UI's withdrawal | A token batch's or a name's block: the free check only (their reads ride an address's or a name's circuit, D39); a block a transaction names (G12 asks again on its own circuit); `Store.forkWarning` in the UI; the binding version over an honest chain |
| `Head(final)`: the anchored or finalized EL header (D41) | G13, G17, G18 |
| "Your node refuses proofs at block N", the refused read's block (D42) | `just kani`'s `lkd-k256` harness (pre-existing) |
| D13 restated: deadlines that hold under the planner's concurrency (D43, the review's finding 12) | The launcher forwarding `pp`, `shield`, `unshield`, `history` |
| Freshness where a value gates or pays (D58) | A key set naming its origin's circuit (per-origin reorg checks: an ABI change) |
| D1 fails closed for a command `lkd` did not start (D60) | Rendered lines (`Spec.OverviewText`, D49); H_lc, sockets, timeouts, caches, screens (tested) |
| The UI's halves at the value level (D49 to D51): what the refined re-checks accept given what was asked, H_lc-free, and that composed with `lkd-lc`'s halves for balance and nonce (kinds 1, 2, final), tokens, pins, pools, inclusion, `Head`, `BlockHash`, the snapshot records the UI writes; D1's gate kernel with each flow's needs and its configured input; D3's and D7's keep rules, outcome 1 included | Key-set tags 8, 9 and query `0x0e`: still reserved, unused |
| ENS and prices read at the anchor (D32's follow-up, D44 to D46); ENS names as facts, type 3 (D5's, D47, D48) | The direct route's live run unless the user asks (D52) |
| `e2e-lc-live`, mainnet and Sepolia over Tor, read-only, with the survey's lines; `lkd-e2e --lc-survey` (D52) | A release-binary live run on this host, whose seccomp refuses `mlock` (the user's `just e2e-lc-live` on a host that locks memory, D52) |
| `INVARIANTS.md`, `AGENTS.md`, `00-plan.md`, `01`, `03`, `04`, `08`, `15`, `17`, `18` and this file's status, final | |

### Decisions (LC9)

Rows marked **the user's** are put to the user once at BASE ([The decision gate](#the-decision-gate-lc9)); meanwhile tracks build the default, its code, tests and e2e steps in commits whose subject ends `(Dn)`, so a no reverts those commits or swaps the one constant or arm named.

| # | Decision | Whose call |
|---|---|---|
| D38 | G9's transport: query `BlockHash(n, final)` (`0x0f`) answered `BlockHash` (`0x8e`) at P, the anchor's EL header (final 0) or the finalized one (final 1), as `Head(final)` names them: proved (P's own hash when n is P's number; else `History.blockHash` of EIP-2935's slot under P's state root, read by key set 6 `History(n)` at P's EL hash), ahead (n past P's number), too old (P's number > n + 8191); the UI re-checks the certificate (`lc_check::history_hash`). Key set 6, allocated on `Head` and never issued, is issued on `Shared` (egress 10i restated: `Head` carries the block number and headers only): on `Head` it would share the circuit of the head cross-checks (`HeaderAt`) the UI makes right after an address's `Account` answers, so an endpoint could tie a review's batch block to that address. Its layout is unchanged (tag 6, 8 bytes: `crates/lc-core`'s `request_len` and the ABI untouched). netd sends it to the endpoint P's block hash picks (`endpoint_for(hash, attempt)`, as `ElHeader(P)` goes), not by the contract, so no endpoint collects every block this install checks. Rejected: a core-side reorg flag (a `Status` layout change, nothing for the UI to check); a key set naming its origin's circuit (a token batch's check on its owner's: `request_len`, an ABI change) | Decided (egress review) |
| D39 | G9 in the UI (`lkd_ui::reorg`). Noted: the blocks the last pin and pool batches were proved at while shown (D21, G16), shared reads. Never noted, the free check only: a token batch's block (its reads ride `Account(owner)`, and a `History` read on any other circuit would tie the owner to the check; a token is green only while fresh), a name's (its reads ride the name's circuit; a name is looked up again at each lookup), a block a transaction names (G12 asks again on its `Broadcast(n)` circuit until a final proof is kept, D3), a balance or nonce line (every refresh proves it again). For each noted (N, h): `BlockHash(N, 0)` at the first refresh whose anchor is ≥ N + 2 and again at the first at which N ≤ F, both at the anchor (never at F, where the snapshot pass's `Account` reads go), asked as a pin batch is: after `proved::wait_shared()` (never at the anchor of an `Account` or `Token` read of this UI), at most `reorg::ASKS` (4) a refresh, newest first, the rest at the next; free: any anchored answer whose own block is N with another hash. Another hash withdraws every value at (N, h): yellow "Block N was replaced (reorg, not final): values proved there withdrawn; proving again at block M", proved again at the next refresh (a review's pin batch at once); nothing persisted changes. **Cost**: up to two storage proofs of EIP-2935's slot per shown pin or pool batch block, on the `Shared` circuit that read the batch, at an anchor no `Account` read of this UI used, each to the endpoint that anchor's hash picks; the request tells that endpoint that some wallet showed a shared batch at N (a review, the session's start or a pool sync), which the endpoints that served the batch knew; it names no address. A no: the free check only (`ASKS = 0`) | **The user's** |
| D40 | `AccountFinal(a)`: the anchored `Account` (`0x82`, kind 2) at F, the store's finalized header: anchor ⟨F's number, F's EL hash, the anchor's signers, the committee's size⟩, `anchoredFields s l st F true`, read at F's EL hash on `Account(a)`. The UI asks it through `proved::final_account` at most once an epoch per address with a settled or unresolved transaction, re-checked as final (`lc_check::account`: the chain's committee size, finalized = number) and cross-checked at F (D35), for G11's "settled at block F, final" and for D7's outcome 1 (settled by nonce), which it now rests on in place of `MakeSnapshot`'s record: the UI's check of that record bound its header to its own Keccak only, so outcome 1 rested on H_lc alone and on no cross-check; it is kept only for an accepted final answer whose block F cross-checked agrees (`inclusion_keep::settled_keep`). Never for freshness or `may_replace`. `Plan.want` keeps reads at every hash the context names, so `Account`, `AccountFinal` and `MakeSnapshot` no longer evict each other | Decided (D25; storage review) |
| D41 | Query `Head(final)` (`0x10`) answered `Head` (`0x8f`): the anchored (0) or finalized (1) EL header and its anchor, from what the planner holds (one `ElHeader` an anchor, which anchored reads fetch anyway); what the UI binds by-number reads to (D44) and names blocks with (D42) | Decided |
| D42 | netd reads a JSON-RPC error's code and message on `eth_getProof` (`ElProof`, `ElStorage`): reth's `-32602` "distance to target block exceeds maximum proof window", a message containing "proof window", "missing trie node" or "historical state" (geth; besu, erigon and nimbus answer `-32000`, nethermind `-32002`), or code 4444 (execution-apis' "pruned history unavailable", which its issue 953 proposes for `eth_getProof`) become `Failure::Pruned`, matched on the raw text and kept sanitized (`rpc::sanitize`, as every node error); on a block or receipts read a 4444 (EIP-4444's history expiry) stays `Node`. From your own node only (source 255) the channel's code 12 `Window`, else 4 `Node` (rotation). The core ends the read at once: lcproto error 9 `NodeWindow`. The UI names the refused read's block: F (`Head(true)`) for `AccountFinal`, `MakeSnapshot`, `MakeTokenSnapshot` and a final `Included` or `BlockHash`, the anchor (`Head(false)`) otherwise: "your node refuses proofs at block N (reth: --rpc.eth-proof-window; geth keeps the last 128 blocks' state)"; Settings' "Execution proofs" says it beside the head cross-check (the per-endpoint record is dropped); D1 counts it unproved; `lkd doctor` keeps "at least 256 for a reth node" and adds that final proofs read the finalized block, 64 to 96 blocks back and more under non-finality. The message rule only names a reason, never changes a value | Decided |
| D43 | D13 restated: `maxJobs` 2, `perStep` 2, `maxStorageWithBody` 1 (netd is serial: more in flight only queues there, outside the planner's priorities, at no gain in throughput); netd's turn by rounds: after serving a datagram netd serves one frame from each UI connection that had one waiting then, in turn, then the next waiting datagram (a datagram arriving while netd is idle waits only for the frames already waiting, one per connection); netd sends `Started` (`0x83`) as it begins serving a decoded `Fetch`; the shell's deadline is `QUEUE_LIMIT` 120 s from sending until `Started`, then netd's deadline for the kind + 3 s (a `FetchPage`: 123 s from sending); the shell sends a fetch only while fewer than two of its fetches are queued in netd (sent and not started, awaited or timed out, a timed-out one counted until its page or failure, its `Started` not ending the count, or 2 × `QUEUE_LIMIT` from its sending, at least its kind's service and the margin from that `Started`), else the core hears `NotSent` at once, so at most one of its datagrams is ahead of a fetch; the core's `jobMs` 140 s, `bodyJobMs` 155 s (backstops above the shell); the constants in `lkd_verified::deadlines`, specified in `Spec.Deadlines` and ordered by `Refinement.Deadlines`; the UI's netd `TIMEOUT` is `deadlines::UI_NETD_TIMEOUT_MS` (40 s, unchanged), a budget like its other windows, which keep their values (it bounds no UI frame's wait, which netd does not limit: tested); D1 unchanged. The deadlines hold while the UI frames netd serves between a fetch's sending and its `Started` (at most two rounds) take at most `QUEUE_LIMIT − BODY − MARGIN` (90 s) together (tested); past that a fetch times out and is asked again: delay, never a wrong value. Rejected: a total deadline on every UI frame (it would cut today's reads and broadcasts); netd queue accounting with a `Busy` code | Decided |
| D44 | D32's follow-up, built in the UI instead of `lc9/quorum-pins` as deferred (key sets 8 and 9 read by `lkd-lc`): after D37's wait (D45) the UI asks `Head(false)`, re-checks it (`lc_check::head`) and its freshness (D58), then asks netd `ProvedNameAt`/`ProvedReverseAt`/`ProvedPricesAt` (`0x21` to `0x23`) with `At {number, state_root}`: netd's existing `EnsProof`/`PriceProof` reads at that number (an address's reverse record, and its primary name's forward read, first to the endpoint that address picks; a typed name in turn, as today), each part checked under that root, answered `Parts` (`0x95`); `ens::forward`, `reverse`, `primary`, `prices::quote`, `sqrt_price` under the anchored root and the header's timestamp, then D35's cross-check, then by outcome ([the table](#names-prices-and-the-reorg-check-d39-d44-to-d48)): proved, fresh and agreed: green, "proved at block N, signed by s of 512 of the sync committee"; a refusal proved under the anchored root (ENS: `Code`, `Unregistered`, `Expired`, `Migrated`, `NoResolver`, `Resolver`, `NoAddress`, `NoName`, `Malformed`, `Mismatch`; prices: `Code`, `Moved`, `Malformed`) or a cross-check disagreement at or below F: red, no address, never asked of the quorum (of one endpoint, since 2026-10-28); a cross-check disagreeing above F or unanswered: the anchored address, yellow, behind D46's rule; a transport failure (`Head` pending or an error, `NodeWindow`, netd not answering, the At parts not verifying under the root), a stale anchor or the clock behind: the quorum path, behind D46's rule. The At reads go to the same provers as the quorum's, so whoever controls them can fail the anchored read and reach the quorum path: "proved refusals are final" holds only when the anchored read succeeds, and D46 makes what follows typed, never silent. Each name keeps its provenance (the anchored block and signers, or k of n) wherever it shows. No lcproto, channel or egress change. **Cost** against the deferred design: names and prices rest on one Aeneas-refined check, the UI's, under a header `lkd-lc` vouches for, without `lkd-lc`'s own Lean read beside it; a compromised `lkd-lc` with one endpoint silent on `HeaderAt` gets a yellow address behind D46's rule, never green; and a primary name read on the quorum path while a light client is configured is read again (its address's reverse lookup and its name's forward one) an epoch later, as built only while the light client anchors with a fresh anchor as the UI last saw it (`names::anchors_now`, the integration's review: before it, every such name was read again every epoch while the light client was down, catching up or stale, which proved nothing and repeated the batch's lookups some 225 times a day). A no reverts the `(D44)` commits: names and prices stay on the quorum head, labelled k of n, and `lc9/quorum-pins` as deferred follows LC9 (two key sets, `request_len`, egress 10j). 2026-10-28: the quorum is removed; where this row says the quorum path or k of n, read one endpoint's path, "on one endpoint's word" | **The user's** |
| D45 | A typed name and the primary-name thread wait `proved::wait_shared()` (one slot + 0 to 6 s after the last `Account` answers) before `Head` and the read. **Cost**: up to about 18 s on a review just after a refresh. A no: `names::WAIT_SHARED = false`. Prices wait under D37 regardless | **The user's** |
| D46 | A light client configured but no anchored, fresh, agreed read (not anchored, not fresh (D58), the clock behind, a transport failure as D44 lists, or the cross-check above F disagreeing or unanswered): a name shows on one endpoint's path and label ("on one endpoint's word"; the quorum's until 2026-10-28) (or as the anchored address, for the cross-check's cases) with "(not proved at the anchor: <why>)" yellow, and a send to it asks `W` (anyway typed, never `--yes`) naming why (`names::UNANCHORED_SEND = Act::Ack`); prices are shown so, nothing asked (they gate nothing). Without a light client configured, today's path and review, unchanged. **Cost**: one typed acknowledgment whenever the anchored read fails, which whoever controls the provers can cause at will. A no: `Act::Block` (such a send blocked) or `Act::Pass` (the yellow line only), one constant | **The user's** |
| D47 | D5's follow-up, built in the UI instead of `lc9/ens-facts` as deferred (`MakeNameSnapshot`, query `0x0e`, `lkd-lc` reading ENS): type-3 facts made by the UI in the snapshot pass at the pass's finalized block F (D44's reads with `At` = F's number and state root, routed as D48 says, re-checked), a reverse and a forward fact, each in a record of its own with the pass's update and header; `lkd-lc`'s held rule is generic (`Lc.nameHeld`: each nonempty part's account and each carried key's value under the header, which `lkd-lc` binds to a committee-finalized header); the ENS meaning is the UI's re-check on load; query `0x0e` unused; `keyd`'s retention unchanged. **Cost** against the deferred design: a name fact's ENS meaning rests on the UI's refined check alone. A no reverts the `(D47)` commits; `lc9/ens-facts` as deferred follows LC9 | **The user's** |
| D48 | Which names persist: the selected account's primary name (a reverse and a forward fact) in each pass while it has one, shown at start "(snapshot at block F)". Its reads at F go after `proved::wait_shared()` past the pass's account reads, both first to the endpoint the selected address picks (the one proving its account at F), each on its name's circuit: no other endpoint learns the address from them, and that one learns nothing it does not already serve. The pass writes its name records before its account and token records, so `keyd`'s eight records a block (`MAX_PARTS`, the newest kept first) drop the names first. **Cost**: about 10 storage proofs a pass on the `Name` circuits, to that endpoint; 40 to 90 KB a pass in `keyd`'s encrypted journal (a wrapped name about 35 KB, the 2017 registry 6 KB more), so `keyd`'s 8 MiB a session (`SESSION_SNAPSHOTS`) is reached in about a day of one session instead of several days (past it, snapshots stay in memory and the next start shows the one written when the cap was hit); a pass with more than six account and token records keeps no name that pass; a fact that does not fit one record beside a full update (about 27 KB, after a period change) is skipped that pass and said, "name not kept: too large for one record". Rejected: making the facts only once a day (`keyd` keeps the two newest blocks' records, so older name records would need a retention change, a storage review). A no: `snapshot::NAMES = 0` | **The user's** |
| D49 | The UI's halves at the value level: 25y's headline is what the refined re-checks accept, H_lc-free, given what the UI asked (the identity, the anchor's shape with the chain's committee size, the header by hash and number, the reads at the keys `Pins` derives for the index, owner or address asked, the verdict), stating every value the UI shows, gates on or keeps; composed with `lkd-lc`'s halves under H_lc, what the UI shows, gates on or keeps is what `Spec.Mpt`/`Spec.Header`/`Pins` read at an `AnchorProved` block, and for the facts of the snapshot records the UI writes, at the finalized header of a store `Reaches` gives (each fact one an `lkd-lc` record carried; their merging into the records written and D47's name records, glue, tested); the rendered text is tested. 25p's `Ui.balance_line_sound` (`Spec.OverviewText`), never built in LC6, is restated as `Ui.account_sound`. A no: line-level statements need the rendering moved into `lkd-verified` (L), a track after LC9 | **The user's** |
| D50 | The UI halves' scope: kinds 1 and 2 and final; H_6780 named for a proxied token; the UI's checkpoint a hypothesis (none, or the configured one); the committee size from `lc_check`'s table (512 on mainnet and Sepolia, 32 on the development chain), never an answer's `of`; no binding version | Decided |
| D51 | Modules: `lkd_verified::lc_check` (re-checks taking what was asked, the committee table, freshness, the snapshot records' re-checks `record_account` and `record_tokens`), `pin_gate` (D1's kernel with each flow's needs, the configured input (D60), freshness, the cross-check's verdict), `inclusion_keep` (D3's and D7's keep rules, outcome 1 from `AccountFinal`); `Spec.LcCheck`, `Spec.PinGate`, `Spec.InclusionKeep` with their acceptance theorems; composed in `LkdProofs.Lc.Ui`; the UI keeps its public signatures, words and screens | Decided |
| D52 | The live run: mainnet and Sepolia over Tor, fresh wallets of anvil's words, read-only, once at the integration, after the targeted e2e and before the rest of the suite (a wallet fix it finds is then covered by the one full suite). Binaries: the release build when `lkd-keyd --check-mlock` succeeds (RLIMIT_MEMLOCK's soft limit raised to its hard one first); on this host, whose seccomp refuses `mlock`, the debug build of verification step 10 with `lkd start --no-mlock`, the one development option allowed, on keyd only, every verdict line saying so; the release-binary run is the user's `just e2e-lc-live` on a host that locks memory. Stage 1 alone (`lkd-e2e --lc-survey`: curl over the harness's own tor, read-only, no wallet) runs once in lc9-deadlines and once at the integration before the live run, neither counted. Pass criteria are the wallet's: k ≥ 2 of n sources agree; verdicts against the oracle's recomputation at the same block hash (a disagreement with the table, "table drift", reported, not failed); the budget judged on the light client's classes. A failed stage is probed at once with the failed requests, through the wallet's tor with their circuits' credentials, at the wallet's deadlines (all answered: FAILED, the wallet's; any not: inconclusive, with the probe's error); exit 0 green, 3 inconclusive, 1 failed; at most two runs of a chain in all (one rerun of an inconclusive chain after a pause, or one after a fix). LC9 is accepted when both chains are green, or when the user accepts an inconclusive one; a debug-build green is recorded as such, and the fast-forward waits for the user's word on it. The direct route only with `LKD_LIVE_DIRECT=1` (this machine's IP to beacon sources). A no: the integration runs `lc-live-dry` and the survey only; the live run is the user's | **The user's** |
| D53 | Open decision 9: record public beacon sources over Tor as `lkd init`'s default, own beacon node or none opt-in? Until answered the row stays open, noting what `lkd init` offers | **The user's** |
| D54 | `AGENTS.md`: a fast version may be proved equal to its readable one in `LkdProofs` (Mathlib), listed in `Audit.lean`, second reviewer (open decision 6, as LC4b's BLS layer). Until answered: described as open decision 6's practice | **The user's** |
| D55 | The received-funds notice: not built (nothing exists); listed for later. A yes starts a follow-up after LC9, built on `AccountFinal` | **The user's** |
| D56 | One stage, six tracks, posts within the stage (`WIRE_RS` only once the refinements build again, `SNAPSHOT` once `Refinement.Snapshot` does), targeted checks once; one `Funs` build on the machine at a time (`$F`); one integration: master first, full verification once, the live run once (D52) before the rest of the full e2e, which runs once and at most once more; lc9-ui-a's composed theorems (`UI_COMPOSED`) land as a Lean-only merge when they come after the verification | Decided |
| D57 | `AGENTS.md` also gains: `LkdLcDev` (dev-only) and its export `lkd_lc_init_dev` in `LkdLcDev/Ffi.lean` (`dev-insecure` only) in the `@[export]` rule and the ABI paragraph (`proofs/core/lakefile.lean`'s "it has no export", "its two exports" and "so far" corrected); the Runtime Lean bullet keeps this line's text and gains master's Keccak rule restated for `LkdBase.KeccakFast` (a runtime library's module that calls `keccak256` imports it, directly or through `LkdBase.Common`, or `check-core.sh`'s rule 5 fails; "the first four rules" become five); the Secrets line restated: every class egress allows, each over Tor or to your own node: JSON-RPC (10a, 10d to 10i), the relayer class (Tornado and Privacy Pools relayers, `relayer.rs`), the ASP class (`asp.rs`) and the beacon class's typed `GET`s; the one exception the opt-in direct route for public beacon data (decision 28, 10i, 26c); a new class or route needs a second reviewer; the test-only unsafe modules gain `crates/ui/tests/sandbox.rs`; the second-review classes (egress, sandboxes and `lkd-beacon`, `bump-tor`/`bump-roots`, journal kinds, the pin table's data, the moved UI kernels, `proofs/ABORTS.allow` entries and `scripts/CheckCore.lean` rows, restated statements while `lean-gate` is skipped); network tests not in `ci`; the lock scripts stay machine-local | Decided |
| D58 | Freshness where a value gates or pays: an anchored value counts as proved now only while `lc_check::fresh` holds: the UI's clock at most `lc_check::gate_bound_s(chain)` past the timestamp of the header the UI re-checked, and `lkd-lc` not in phase 6 (clock behind) as the UI last saw it. `gate_bound_s`: 768 s on mainnet and Sepolia (F), 90 s on the development chain, by the rule that it is at least `PIN_BATCH_WITHIN` and two slots, so a batch the UI accepts in time is fresh when it arrives. A stale matched pin is unproved: deposits and PP relayed withdrawals block naming its age, the other flows get `W`; a review whose batch turned stale asks again once the anchor has moved past the stale batch's block, keeping the stale verdict meanwhile; the pools' "the pool knows it" line, a token send's gate (`W` only) and D44's names and prices (not proved at the anchor, D46) follow it; labels keep F's display rule. **Cost**: while the light client stalls past F, deposits and PP relayed withdrawals block; H_clock's residual: a clock set back that `lkd-lc` does not see as behind. A no: a longer bound (`lc_check::GATE_BOUND_S`, one constant), never none | **The user's** (mixing review) |
| D59 | D4's fallback within a session: once every endpoint that took a broadcast refused or timed out, G12's reads go to the endpoint the transaction's hash picks, on a circuit of their own, which learns that a wallet asked for that block (as after a restart, which the user accepted). A no: within a session G12 never asks past the broadcast's endpoints (shown "seen, not yet proved" until the next session); one arm of `Upstream::g12_endpoint`, lc9-wire's on a no | **The user's** |
| D60 | D1 for a command `lkd` did not start (typed in another terminal, without `LKD_SETTINGS`): "no light client" only from `lkd`'s settings, from netd's word that it runs with no beacon source (`Health.beacon` 0: a local frame, nothing is sent) or from `lkd-lc`'s own status (running, no checkpoint, where `lkd` passed no settings); a missing or silent `lkd-lc` socket is otherwise "light client not answering" (unproved): deposits and PP relayed withdrawals block naming it, the other flows get `W`. `pin_gate::light(configured, socket)` decides it, proved in `Spec.PinGate`. Today `lkd-lc` returns before binding its socket when its evidence cannot be read, and such a command then passed with "code not checked: no light client" while the TUI, which has the settings, blocked. **Cost**: such a command blocks while `lkd-lc` is down or refused to start. A no: today's inference (a missing socket is no light client), one arm | **The user's** (mixing review) |

### What this section overrides (LC9)

- Line 3's status (base: "LC0 to LC8 built and proved as each milestone's As built says (2026-10-27); LC9 designed below, not built"; the docs pass: as built); open decision 23's and LC7/LC8's D4 rows, `06-tor.md`'s G12 exception, `INVARIANTS.md` 10i's note: D4's fallback accepted as the user worded it, D59 pending; the Inclusion as built (phase 2) line saying netd fetches G12's block and receipts "from `el_endpoint(tx, attempt)`": `g12_endpoint` (base).
- Frame layouts' reserved ranges (queries `0x0f`+, answers `0x8e`+, codes 9+), the channel's replies and codes, `decode_reply`'s "1 to 11", What 25o and 25q prove; The node's proof window; Failure states' window row; Settings' "Execution proofs" bullet; `crates/ui/src/settings.rs`'s notes (lc9-wire).
- LC1's core's "`AccountFinal` … `Unsupported`" (without a light client only), `Step.lean`'s doc, `PlanStorage`'s "`History` is not issued", "(allocated, not issued: D25)"; G7 to G9 (the "`History(N)` on `Head`, keyed by the number only" passage), Egress v8's key-set table row for `History(N)` and the Privacy section's "G9's history proofs on `Head`", the summary table's 10i row; the helios table's G9 row (25x, LC9, D39's scope) and G11's (`AccountFinal`); G11's call sites and Never-stuck screens' "settled at block…" line (lc9-history; the UI's withdrawal lc9-ui-b).
- FFI and the runtime (netd's loop, the shell's deadlines, `ANSWER_WITHIN`'s text), LC7/LC8's D13 row and Constants, the planner's as built, Testing's Live paragraph and its lc-netd-busy and lc-killed-mid-* timings (lc9-deadlines).
- The composed theorems (`Lc.account_sound` stays LC1's kind-1 theorem; the anchored one is `Lc.anchored_sound`, with `anchoredFinal_sound`; `Ui.balance_line_sound` becomes `Ui.account_sound`), their As built, Tested not proved, 25p's UI clause, 25s's, 25t's and 25u's UI clauses (lc9-ui-a); G14's gates and D1 (the configured input, D60), D3/D7 as built (outcome 1 from `AccountFinal`), What it does not protect against's G9 sentence, Failure states' stale and reorg rows (lc9-ui-b).
- Snapshot records' "`3` is reserved", G19's "no ENS name is kept" and the helios table's G19 row, open decision 25's, D5's, D25/D32's rows, What the UI trusts' "one specification compiled by two toolchains" (names and prices under D44), Trust per route and per attacker's "A compromised `lkd-lc`" row and "What a node or a colluding quorum can no longer do" (since 2026-10-28 "a node or a lying endpoint"), `17-ens.md` (its anchored reads, "What is proved, and trusted"), `18-prices.md`, `08-accounts-journal.md`'s `Snapshot` row (token and name facts), `INVARIANTS.md` 15j (lc9-ens).
- Open decisions 1 to 28 (each row decided and built, or open with what was built; 2 and 9 by D53), Failure states' rows against `light.rs`'s lines, Risks' "Few sources", Tooling's state, Milestones, the survey's "not over Tor", To confirm 6 and 7, Other documents (each marked done), `proofs/core/lakefile.lean`'s `LkdLc` and `LkdLcDev` docstrings, `00-plan.md`, `01-keyd.md`'s Keccak passages (`LkdBase.KeccakFast`), `03-wallet-ui.md`, `04-verified-reads.md`, `15-desktop-window.md`, `AGENTS.md`, `INVARIANTS.md` (its Keccak-256 row included) and `Audit.lean`'s Keccak comment (the integration's docs pass).

### Frames (LC9)

Common rules as in [Frame layouts](#frame-layouts); bodies include the tag; every new answer's anchor is kind 2, 103 bytes, `final` 1 at the finalized header.

| Tag | Query | Fields | Body | Answered by |
|---|---|---|---|---|
| `0x03` | `AccountFinal(a)` (exists) | address (20) | 21 | `Lc.accountFinalLight`: `0x82` kind 2, final 1 |
| `0x0f` | `BlockHash(n, final)` | block number (8), final (1: 0 or 1) | 10 | `Blocks.blockHashLight` |
| `0x10` | `Head(final)` | final (1: 0 or 1) | 2 | `Blocks.headLight` |

| Tag | Answer | Fields after the tag | Body |
|---|---|---|---|
| `0x8e` | `BlockHash` | identity (72), anchor (103), block number (8), status (1), block hash (32), proving header length (4), header, history-account length (4), nodes, history-slot length (4), nodes | 229 + P + A + S |
| `0x8f` | `Head` | identity (72), anchor (103), header length (4), header | 180 + H |

`0x0e` stays reserved (unused, D47), `0x11`–`0x7f` and `0x90`+ reserved. `BlockHash`: P the anchor's attested header (final 0) or the finalized header (final 1); status 0 proved (hash nonzero, header 1–2,048 bytes, history proofs present exactly when n is not P's number), 1 ahead (n past P's number), 2 too old (P's number > n + 8191), 1 and 2 with hash zero and header and proofs empty; the anchor names P, `final` as asked. `Head`: header 1–2,048 bytes, `final` as asked. Error 9 `NodeWindow`. Lean `Query.blockHash (n : Nat) (final : Bool)`, `Query.head (final : Bool)`, `BlockHashCert {header account slot : ByteArray}`, `BlockHashAnswer {anchor : Agreed, number : Nat, status : UInt8, hash : Bytes, cert : BlockHashCert}`, `HeadAnswer {anchor : Agreed, header : ByteArray}`, `Answer.blockHash id x b`, `Answer.head id x h`, `nodeWindow := 9` (`codeOk` to 9), `blockProved 0`, `blockAhead 1`, `blockTooOld 2`; Rust the same in Rust case (`Query::BlockHash { number, is_final }`, `Query::Head { is_final }`, `Answer::BlockHash { identity, anchored, block }`, `Answer::Head { identity, anchored, head }`, `TAG_BLOCK_HASH`, `TAG_HEAD`, `TAG_BLOCK_HASH_ANSWER`, `TAG_HEAD_ANSWER`, `ERR_NODE_WINDOW`, `BLOCK_PROVED`, `BLOCK_AHEAD`, `BLOCK_TOO_OLD`), a certificate plain fields with an absent part empty.

**Channel.** Reply kind `0x83` `Started`, nothing after the kind, 13 bytes: netd sends it as it begins serving a decoded `Fetch` (never a `FetchPage`, never an undecodable datagram), dropped if it would block; the shell takes it, the core never sees it. Code 12 `Window`: your own node refused the proof (pruned, or outside its proof window), written only for a request your own node served; 13+ reserved; `decode_reply` bounds codes to 1–12. Key set 6 `History(n)` keeps its layout (tag 6, 8 bytes): `lkd-lc` issues it for the first time, egress puts it on `Shared`. Lean `Channel.Outcome.started`, `Channel.failWindow := 12` (`failOk` to 12); Rust `Outcome::Started`, `REPLY_STARTED`, `FAIL_WINDOW`.

**Snapshot fact type 3** (after types 1 and 2; a lower type after a higher refused): type (1: 3), direction (1: 0 forward, 1 reverse), subject length (1: 1–255) and subject (the normalized name, or the address), part count (1: 5 forward, 3 reverse, positional as `ens::Bundle`/`ReverseBundle`), per part: contract (20), account (88), proof length (4), nodes, key count (1: 0–10), per key: key (32), value (32), length (4), nodes; an empty part is all zero or empty. Held (`Lc.nameHeld`) exactly when every nonempty part's account is `Spec.Mpt.accountB`'s under the header's state root and each key's value `Spec.Mpt.storageB`'s under that account's storage root. Lean `Snapshot.NamePart {contract : Bytes, account : Spec.Mpt.Account, proof : ByteArray, slots : List (Bytes × Bytes × ByteArray)}`, `Snapshot.NameFact {reverse : Bool, subject : Bytes, parts : List NamePart}`, `Record.names : List NameFact := []`, `Snapshot.maxKeys := 10`; Rust `snapshot::NamePart`, `NameFact`, `Record.names`.

**netproto** (UI ↔ netd): `0x21` `ProvedNameAt { at, via, name }` (8, 32, 20, 1–255; `via` zero: the provers in turn, as today; else the endpoint the address `via` picks first, then in turn), `0x22` `ProvedReverseAt { at, address }` (8, 32, 20; the endpoint the address picks first), `0x23` `ProvedPricesAt { at }` (8, 32), `at` netproto's existing `At`; reply `0x95` `Parts` (the parts as `put_parts` writes them). `Health` gains `beacon` (1: how many beacon sources netd was started with) after `route` (D60). Egress unchanged for these: today's `EnsProof` (`Name(node)`) and `PriceProof` (`Shared`) at a block number.

### `lkd-lc` (LC9)

`accountFinalLight` is `accountLight` at F = `st.finalized`. `Plan.want now named h fin a p` keeps reads at every hash in `named` (the context's: the anchor's and the finalized header's EL hashes), so `Account`, `AccountFinal` and `MakeSnapshot` no longer evict each other; its callers pass the context's (`accountLight`, `accountFinalLight`, `makeSnapshot`'s call, `Storage`'s `MakeTokenSnapshot` read). `headLight`: P the anchor's attested header or F; the answer once the planner holds P's EL header bound to P, else its error, or `Pending` with the header wanted. `blockHashLight`: P by the query's `final` as `headLight` picks it; ahead and too old at once; n = P's number proved without a proof; else a `PlanStorage` read of `.history n` at P's EL hash (`keysOf`: EIP-2935's contract, `Pins.historySlot n`; a hash-only read gets a key set `keysOf` never derives) answered only when `History.blockHash` gives a hash, else `Refused`. `Plan.Failure.window` (lcproto code 9): `Plan.fail`, `PlanStorage.fail`, `PlanIncl.fail` end the read at once on channel code 12 (`Wire.Channel.failWindow`). Egress (proved, 10i restated): `keysGroup (.history _) = .shared`; `publicGroup_head` again says the head's group holds the block number and headers only. netd (tested): key set 6's endpoint is picked by the request's block hash (`lc_storage::endpoint_key`), as `ElHeader`'s.

```lean
-- LkdProofs.Lc.Anchored: `anchored_sound` (25p) gains `(hx : x.isFinal = false)`; new:
theorem anchored_final_iff (h : .answer c (.anchored id x ans) ∈ (step (run cfg ins) i).2) :
    x.isFinal = true ↔ ∃ frame, i = .query c frame ∧ decodeQueryB frame = some (.accountFinal ans.address)
theorem anchoredFinal_sound (h : .answer c (.anchored id x ans) ∈ (step (run cfg ins) i).2)
    (hx : x.isFinal = true) : id = configIdentity cfg ∧
    (∃ frame, i = .query c frame ∧ decodeQueryB frame = some (.accountFinal ans.address)) ∧
    ∃ l st L hdr, AnchorProved cfg (run cfg ins) l st L ∧
      Anchor.bind l.chain st.finalized ans.header = some hdr ∧
      ans.anchor = ⟨hdr.number, st.finalized.elHash.data.toList, L.signers, l.chain.preset.committeeSize⟩ ∧
      Spec.Mpt.account hdr.stateRoot ans.address ans.proof.data.toList = some ans.account ∧
      x.slot = st.finalized.beacon.slot ∧ x.beaconRoot = st.finalized.root.data.toList ∧
      x.finalized = hdr.number ∧ x.parent = (Store.elTag l.chain st.finalized == .parent)
-- LkdProofs.Lc.Blocks
theorem head_sound (h : .answer c (.head id x a) ∈ (step (run cfg ins) i).2) :
    id = configIdentity cfg ∧ (∃ frame, i = .query c frame ∧ decodeQueryB frame = some (.head x.isFinal)) ∧
    ∃ l st L P hdr, AnchorProved cfg (run cfg ins) l st L ∧
      ((x.isFinal = false ∧ P = L.header) ∨ (x.isFinal = true ∧ P = st.finalized)) ∧
      Anchor.bind l.chain P a.header = some hdr ∧
      a.anchor = ⟨hdr.number, P.elHash.data.toList, L.signers, l.chain.preset.committeeSize⟩ ∧
      x.slot = P.beacon.slot ∧ x.beaconRoot = P.root.data.toList
theorem blockHash_sound (h : .answer c (.blockHash id x b) ∈ (step (run cfg ins) i).2)
    (hs : b.status = Wire.blockProved) : id = configIdentity cfg ∧
    (∃ frame, i = .query c frame ∧ decodeQueryB frame = some (.blockHash b.number x.isFinal)) ∧
    ∃ l st L P hdr hp, AnchorProved cfg (run cfg ins) l st L ∧
      ((x.isFinal = false ∧ P = L.header) ∨ (x.isFinal = true ∧ P = st.finalized)) ∧
      Anchor.bind l.chain P b.cert.header = some hdr ∧
      b.anchor = ⟨hdr.number, P.elHash.data.toList, L.signers, l.chain.preset.committeeSize⟩ ∧
      hp = (if b.number = hdr.number then Inclusion.HashProof.anchor else .history b.cert.account b.cert.slot) ∧
      Inclusion.hashOf ⟨P.elHash.data.toList, hdr.stateRoot, hdr.number, x.isFinal⟩ b.number hp = some b.hash
-- and blockHash_status: status 1 ↔ b.anchor.number < b.number; 2 ↔ b.anchor.number > b.number + 8191
```

`Routed`, `step_query`, `step_good`, `step_kinds`, `step_answers_query` cover the three (25r restated); without a light client they stay `Unsupported` (`crates/lc-core/tests/steps.rs`).

### Two netds (2026-10-28)

The rounds below bound how long each side waits for the other; they do not stop the wait. In a
user's Sepolia session (one public endpoint over Tor, the light client on) the light client's
fetches were most of netd's time, and the UI's jobs waited behind them: a refresh took 40 s
whose own `ProvedAccounts` took 10 s. The user chose a second netd over threads in one (netd's
state, its sandbox and the rounds assume one thread):

- `lkd` starts two netds with the same settings (`crates/launch/src/start.rs`, `Netds`): the
  UI's, `lkd-netd.sock`, its standard input nothing, so it has no channel and serves UI frames
  as they come; and the light client's, `--light`, `lkd-netd-lc.sock`, its standard input the
  channel, as netd's was. Each is sandboxed as netd is (nothing in the sandbox changed), started
  again by its own watch, and both are started again together on a change of settings, of
  route, and when tor restarts. The light client's netd's lines are `lkd-netd-lc:`; only the
  UI's says the wallet went offline or came back. Both run the beacon sources' arguments, so the
  UI's netd's `Health.beacon` still feeds D60's gate.
- **Broadcasts.** G12's reads go first to the endpoints that took a transaction's broadcast,
  on that broadcast's circuit (D4), which only the netd that broadcast knows. After each
  `SendRaw` the UI asks its netd `Broadcasts(tx)` (each endpoint's place and broadcast number)
  and tells the light client's `TookBroadcast { tx, took }` (`lkd_netproto`, tags `0x24`,
  `0x25`, reply `0x97`; `crates/ui/src/netd.rs`, `tell_light`). Best effort: when it is not
  told (no light client's netd, or one started again since), its reads go as for a transaction
  broadcast in an earlier session, to the endpoint picked for the hash, on a circuit of its own.
- **Network activity** (Settings → Activity, `lkd network traffic`) reads both netds' traffic,
  the light client's times moved onto the UI's netd's clock by both `Health.uptime_ms`; a netd
  started again drops its own entries only (the light client's netd's are all tagged verified,
  the UI's none). Each endpoint's health is the UI's netd's.
- Each netd keeps its own streams, endpoint backoffs and broadcast numbers; both use the same
  tor and the same isolation credentials, so a group's circuit is the same from either.
- The deadline model is unchanged and still holds, more loosely: the round rule now runs in a
  netd with one client each, so a datagram waits for no UI frame and a UI frame for no
  datagram. The UI's 40 s budget is kept.
- `lc-netd-busy` now checks that the UI's broadcast and receipt poll are answered while the light
  client's netd holds G12's receipts at the node, not after them.

### The deadline model (D43)

| Layer | Constant | Value |
|---|---|---|
| netd | beacon / EL / body deadlines | 8 / 12 / 27 s (`deadlines::BEACON_MS`, `EL_MS`, `BODY_MS`) |
| netd | turn | rounds: after a datagram, one frame from each UI connection waiting then, then a waiting datagram; `Started` before each decoded `Fetch` |
| shell | sent, not started | `QUEUE_LIMIT_MS` 120 s |
| shell | started | the kind's deadline + `MARGIN_MS` 3 s: 11 / 15 / 30 s; `FetchPage` 123 s from sending |
| shell | queued in netd | at most two of its fetches sent and not started (a timed-out one counted until its page or failure, or 240 s, at least its service and 3 s past its `Started`), else `NotSent` at once |
| core | `jobMs` / `bodyJobMs` / `Lc.fetchMs`; `maxJobs` / `perStep` / `maxStorageWithBody` | 140 / 155 / 140 s; 2 / 2 / 1 |
| UI | netd `TIMEOUT` (`UI_NETD_TIMEOUT_MS` = `UI_FRAME_MS` + `BODY_MS` + `MARGIN_MS`); `ANSWER_WITHIN`, `MAKE_WITHIN`, `POOL_WITHIN`; `PIN_BATCH_WITHIN`; `INCLUDED_WITHIN`; `ANCHOR_WITHIN` | 40; 62; 67; 15; 12 s, unchanged, budgets |

`Spec.Deadlines` holds the constants and `serviceMs` over the channel's kinds (bodies `BODY_MS`, beacon kinds `BEACON_MS`, the rest `EL_MS`); `Refinement.Deadlines` refines `deadlines::service_ms` against it and proves by `decide`, for every kind, `QUEUE_LIMIT_MS` + `serviceMs` + `MARGIN_MS` + `CORE_MARGIN_MS` ≤ the core's deadline (a body's `bodyJobMs`, else `jobMs`), netd's deadline below the shell's started one, `UI_FRAME_MS + BODY_MS + MARGIN_MS ≤ UI_NETD_TIMEOUT_MS` (the UI's budget: an order of the constants, no bound on a UI frame's wait, which netd does not limit), and `Plan.jobMs`, `bodyJobMs` equal `JOB_MS`, `BODY_JOB_MS`. Tested, not proved: the UI's netd timeout, the round rule, `Started`, the shell's two phases and its queued-in-netd rule, and the precondition that the UI frames netd serves between a fetch's sending and its `Started` take at most 90 s together (`lc-deadlines`). With the queued-in-netd rule at most one of the shell's datagrams is ahead of a fetch, so its wait before `Started` is at most the rest of a round, one datagram's service (≤ 27 s) and one more round. A netd that died is noticed 120 s after a fetch was sent (123 s for a page). The one-shot `--propose` uses the same two-phase rule. LC1's endpoint path keeps its 64 fetches (delay, never a wrong value). Throughput is unchanged: netd served one request at a time before and after.

### Freshness (D58)

`lc_check::fresh(now_s, timestamp, bound_s, behind)`: `!behind ∧ now_s ≤ timestamp + bound_s`, the timestamp the header the UI re-checked gives (never `lkd-lc`'s `age_ms`), the clock the UI's (the light client's is the same machine's: H_clock), `behind` whether `lkd-lc`'s last `Status` the UI saw was phase 6 (`PHASE_CLOCK_BEHIND`). `lc_check::gate_bound_s(chain)`: `GATE_BOUND_S` 768 on mainnet and Sepolia (F), `GATE_BOUND_DEV_S` 90 on the development chain; the rule: at least `PIN_BATCH_WITHIN` (67 s) and two slots, so a batch the UI accepts in time is fresh when it arrives. Applied where a value gates or pays: `pin_gate::settle(found, crossed, fresh)` (a stale matched pin is unproved: D1 blocks deposits and PP relayed withdrawals naming its age, "proved at block N, <age> ago: not proved now", the others get `W`; a review evaluates it at each keypress (the command line once more at the review's last typed answer, before signing or proving, as built after the integration's review: `main::still_gated`, a gate stricter then answered again) and asks its batch again once the anchor (`light::seen`, or `lkd-lc`'s status) is past the stale batch's block, keeping the stale verdict meanwhile; as built after the integration's review, only while that anchor is itself fresh by `lkd-lc`'s age, `Clock::anchor_fresh`: with the clock ahead of the chain's or the chain stalled every batch is stale on arrival, and the stale words then say the light client's newest anchor is as old, never a batch at each refresh); the pools' "the pool knows it" (`pool_proofs::checks`); D44's names and prices ("not proved at the anchor (proved N min ago)", D46; as built after the integration's review, a send's name counted at each evaluation too: its provenance keeps the anchored header's timestamp, `names::why_not`); a token send's gate (`W` only). Labels keep F's display rule (`light::fresh`, 768 s and 16 s).

### The gate's configured input (D60)

`pin_gate::light(configured, socket) -> Light`: `configured` 0 none (`lkd`'s settings configure none, or, without them, netd's `Health.beacon` is 0), 1 configured (`lkd`'s settings: a checkpoint and a source), 2 sources only (no settings, netd runs beacon sources: the checkpoint unknown); `socket` 0 missing, 1 silent, 2 running without a checkpoint, 3 running. `Light`: none when `configured` is 0, or 2 with `socket` 2; up when `socket` is 3 and `configured` is not 0; down otherwise ("light client not answering", or "not anchored: no checkpoint"): every need unproved. `Spec.PinGate.light_none`: `light c s = none → c = 0 ∨ (c = 2 ∧ s = 2)`. The UI's glue (tested): settings from `LKD_SETTINGS`, else netd's `Health`; the socket's state from `Lc::status`.

### The UI's halves (D49 to D51)

`lkd_verified::lc_check` (Aeneas subset; answer structures, never `lc_wire::Answer`; frozen at LC_CHECK, widened once at UI_ACCEPTS): field-free `Refusal {Chain, Checkpoint, Address, Anchor, Header, Proof, Fields, Storage, Value, History, Verdict}`; `committee_size(chain)` (512 on 1 and 11155111, 32 on 31337, else 0), `fresh`, `gate_bound_s`; `identity_ok`, `anchored_ok` (0 < count ≤ of = `committee_size`, 2·of ≤ 3·count, finalized ≤ number, final ↔ finalized = number when asked final), `header_at`, `account(chain, cp, address, is_final, …)` (kinds 1 and 2, final), `slots` (a `StorageCert`), `words` (a `PoolCert`), `pin(chain, cp, index, …)`, `token(chain, cp, index, owner, …)`, `token_balance` (`settle`'s pure part), `pool(chain, cp, index, …)`, `history_hash(proving, hash, number, n, is_final, block_hash, account, slot)`, `included(chain, cp, tx, number, …)`, `head(chain, cp, is_final, …)` (an anchor and a header, no `lc_wire` answer type), `record_account(chain, address, record)` and `record_tokens(chain, owner, record)` (the snapshot records `lkd-lc` makes, before the UI writes their facts to `keyd`: `recheck`'s and `recheck_tokens`' rules; a record with name facts refused). Each takes what the UI asked and checks the answer names it; each accepted result carries the re-checked header's number, hash and timestamp and every value the UI shows, gates on or keeps. `lkd_verified::pin_gate`: `Flow` (field-free), `Act` with `rank`, `Cause`, `Found`, `Seen`, `Crossed`, `Need {pin, primary, used}` (pin 255: not pinned); `needs(chain, flow, target)` (`target` the flow's contract, the Tornado pool or the token; the Privacy Pools Entrypoint and pool by layout; Multicall3, the announcer and the registry by `egress`'s constants; each with its pin's `uses`), `bit`, `act`, `can_block`, `cause(flow, gates, seen)`, `combine(flow, primaries, causes)`, `checking`, `settle(found, crossed, fresh)`, `crossed(answered, agrees, number, finalized)`, `light(configured, socket)`. `lkd_verified::inclusion_keep`: `Verdict`, `keep(...) -> u8` (255 none, else 0, 2, 3), `settled_keep(final_nonce, n, receipt_known, proved_kept, ours, accepted_final, crossed_agrees) -> u8` (255 or 1), `plausible`, `ranked(records, chain, hash) -> Option<usize>`, `settled_by_nonce`. Every `pub fn` has its `Spec` and refinement.

```lean
-- LkdProofs.Spec.LcCheck: what the UI's re-check accepts, H_lc-free (25y). `Accepted chain cp id x a`:
-- id.chainId = chain; cp = some c → id.checkpoint = c; 0 < a.count ≤ a.of = committeeSize chain;
-- 2 * a.of ≤ 3 * a.count; x.finalized ≤ a.number; x.isFinal → x.finalized = a.number.
-- Every check takes what the UI asked; every result carries what the UI shows, gates on or keeps.
theorem token_accepts (h : token chain cp ti owner id x t = some r) :
    Accepted chain cp id x t.anchor ∧ t.index = ti ∧ t.owner = owner ∧
    ∃ tok p hdr acct, Pins.tokenOf chain ti = some tok ∧ Pins.pinOf chain tok.pin = some p ∧
      t.contract = p.contract ∧ Spec.Header.verify t.cert.header t.anchor.hash = some hdr ∧
      hdr.number = t.anchor.number ∧ r.block = hdr.number ∧ r.hash = t.anchor.hash ∧
      r.timestamp = hdr.timestamp ∧
      Spec.Mpt.accountB hdr.stateRoot p.contract t.cert.account = some acct ∧
      SlotsRead acct.storageRoot (Pins.tokenSlots chain tok owner) t.cert.slots ∧
      (slotValues t.cert.slots).head? = some r.word ∧
      r.found = Pins.verdict p acct.codeHash (slotValues t.cert.slots).tail none
theorem token_balance_accepts (h : tokenBalance tok w = (b, f)) : (b, f) = Pins.balance tok (Pins.toNat w)
-- LkdProofs.Lc.Ui: composed with lkd-lc's half under H_lc (the answer the UI decoded is one a step
-- of the run sent) and the UI's checkpoint (none, or the configured one)
theorem Ui.token_sound (h : .answer c (.token id x t) ∈ (step (run cfg ins) i).2)
    (hcp : cp = none ∨ cp = some (checkpointOf cfg))
    (hui : Spec.LcCheck.token cfg.chainId cp ti owner id x t = some r) :
    t.index = ti ∧ t.owner = owner ∧
    ∃ l st L hdr tok p acct, AnchorProved cfg (run cfg ins) l st L ∧
      Anchor.bind l.chain L.header t.cert.header = some hdr ∧
      r.block = hdr.number ∧ r.hash = L.header.elHash.data.toList ∧ r.timestamp = hdr.timestamp ∧
      Pins.tokenOf cfg.chainId ti = some tok ∧ Pins.pinOf cfg.chainId tok.pin = some p ∧
      Spec.Mpt.accountB hdr.stateRoot p.contract t.cert.account = some acct ∧
      SlotsRead acct.storageRoot (Pins.tokenSlots cfg.chainId tok owner) t.cert.slots ∧
      (slotValues t.cert.slots).head? = some r.word ∧
      r.found = Pins.verdict p acct.codeHash (slotValues t.cert.slots).tail none
```

The rule for every pair: each `*_accepts` names the query inputs the UI asked, each equal to the answer's, and every result field the UI shows, gates on or keeps: account (address, final; nonce, balance, storage root, code hash), pin (index; verdict, the implementation and its code), pool (index; the head words, the root), token (index, owner; the word, its balance and frozen flag by `Pins.balance`, the verdict), included (transaction hash, number; index, success, final), head (final; number, hash, state root, timestamp), blockHash (n, final; status, hash: as built, `blockHash_accepts` takes the block and final flag asked and proves block n's hash, while the answer's own number, final flag and status, its identity and its anchor are its caller's to check, `reorg::judge`, which `Ui.blockHash_sound` takes as hypotheses), the records (address or owner; the account, the token facts). The pairs (each an `*_accepts` in `Spec.LcCheck`, H_lc-free, and a composed `Ui.*_sound`): `Ui.account_sound` with `Lc.anchored_sound` (kind 2); `Ui.accountEndpoint_sound` with `Lc.account_sound` (LC1's, kind 1, 25r); `Ui.accountFinal_sound` with `Lc.anchoredFinal_sound`; `Ui.token_sound`, `Ui.pin_sound`, `Ui.pool_sound` with `Lc.token_sound`, `pin_sound`, `pool_sound`; `Ui.included_sound` with `Lc.Included.included_sound` (the block hash re-checked; the tries `lkd-lc`'s, 25u); `Ui.head_sound`, `Ui.blockHash_sound` with `Lc.Blocks.head_sound`, `blockHash_sound`; `Ui.record_sound` and `Ui.tokenRecord_sound` with `Lc.record_sound` and `Lc.tokenRecord_sound` (the records `lkd-lc` makes, whose facts the UI writes: their header the finalized one of a store `Reaches` gives, not an `AnchorProved` anchor; as built, the records written merge the facts of such records of one block under the same header bytes, `snapshot::split`, and add D47's name records, neither composed); `Ui.settled_sound` (D7's outcome 1: `Ui.accountFinal_sound` with `Spec.InclusionKeep`'s `settled_keep`); `Ui.gate_pass_sound`; `Ui.name_sound`, `Ui.prices_sound` (as time allows). The minimum is account, token, pin, pool, included; what is not proved is said in As built, kept as a documented `def …Statement : Prop`, never `sorry`.

`Ui.gate_pass_sound`: for a funds flow with `pin_gate::light` up, `combine flow (needs chain flow target) causes = pass`, each cause `cause flow (gates p) (settle found crossed fresh)` from that need's `Pin` answer as `lc_check::pin` accepted it for the index `need.pin`, the head cross-check and `fresh now hdr.timestamp (gate_bound_s chain) behind`, gives: every need is pinned, its accepted answer's index is `need.pin`, matched, cross-checked agreeing and fresh, and `chain` is the configured one (`Configured cfg chain cp`, so `need.pin` indexes the configured chain's table); under H_lc its code, at an `AnchorProved` block at most the bound before the UI's clock, is the pinned one. Glue, named in the docstring, 25w and Tested not proved: the flow's target is the transaction's `to`; `configured` and `socket` as the UI reads them (D60).

`Spec.PinGate`: D1's table (by `decide`); `needs` per flow against `LkdLc.Pins` (Tornado flows: the pool's pin and its uses; Privacy Pools' deposits and relayed withdrawals: the Entrypoint's and the pool's, each with its uses; ragequit: the pool's; a stealth send: Multicall3 primary, the announcer; a registration: the registry; a token send: the token's pin) and, by `decide` over every chain's table, no used pin has uses of its own, so one level is the closure; `combine = pass ↔ ∀ c, c = matched`; `can_block → checking = wait`; deposits and PP relayed withdrawals block on every non-matched cause; `cause = matched ↔ seen = proved matched`; `settle = proved matched ↔ found matched ∧ crossed agrees ∧ fresh`; `light_none`. `Spec.InclusionKeep`: kept 0 ⇒ proved ∧ final ∧ agrees ∧ ours; 2 ⇒ too old ∧ ours ∧ plausible ∧ ¬earlier; 3 ⇒ too large ∧ final ∧ agrees ∧ enough sources ∧ ours ∧ ¬earlier; refused, disagrees, ahead, silent, seen keep nothing; `settled_keep` 1 ⇒ ours ∧ accepted final ∧ crossed agrees ∧ the final nonce > n ∧ no own receipt known at n ∧ no proved record kept; `ranked` returns the last proved record when one exists, else the last of the others. Tested: `history::Book::status` (a newer `Mined` record reopens outcome 1), `included::next`'s reopen rule.

### Names, prices and the reorg check (D39, D44 to D48)

Anchored lookup: wait (`proved::wait_shared()`, D37, D45), `Lc::head(false)` re-checked (`lc_check::head`) and fresh (D58), the At request (an address's reverse record and its primary name's forward read first to the endpoint that address picks; a typed name in turn, as today), the ENS or price check under that root and the header's timestamp, `proved::cross_check_block(N, hash, F)`, then:

| Outcome | Shown | A send to the name |
|---|---|---|
| Proved, fresh, cross-check agrees | green, "proved at block N, signed by s of 512 of the sync committee" | as to any address |
| A refusal proved under the anchored root | red, its reason | none: the review cannot confirm |
| Cross-check disagrees at or below F | red, a verifier disagreement | none |
| Cross-check disagrees above F, or unanswered | the anchored address, yellow, the cross-check's line, "(not proved at the anchor: …)" | `W` (D46) |
| A transport failure, a stale anchor (D58) or the clock behind | one endpoint's path and label ("one endpoint's word at block N"), yellow "(not proved at the anchor: <why>)" | `W` (D46) |

Prices take the same rows, shown, nothing asked. `names::Names` keeps each entry's provenance (`Anchored {block, hash, timestamp, chain, signers, of}` or `Endpoint {block, configured}`, `Quorum {block, agreed, endpoints}` until 2026-10-28) and shows it wherever the name appears; the review combines the name's act (`names::send_act`) with the flow's gate, the stricter kept. Without a light client configured: today's path, label and review.

Name facts (D47, D48): in the pass, after the account and token reads at F and `proved::wait_shared()`, `ProvedReverseAt` and `ProvedNameAt` at F's number and state root for the selected address (its endpoint first: `address`, `via`), `ens::reverse` then `forward` back to the address; each fact (the keys `ens::read_slots` derives, values, proofs) in a record of its own with the pass's update and header, within `MAX_RECORD` (else skipped and said), written before the pass's account and token records, kind 7; on load `CheckSnapshot`, then the ENS re-check, "(snapshot at block F)".

Reorg (D39): `lkd_ui::reorg` (`note(n, hash)`, `replaced(n, &hash)`, `ASKS`; the API written at BASE) notes each (N, h) of a shown pin or pool batch; asks `BlockHash(N, 0)` as D39 says, re-checked with `lc_check::history_hash`; marks (N, h) replaced on another hash, or by the free check (any anchored answer at N with another hash, tokens' and names' included); each module holding a value at (N, h) checks `replaced` before showing it green, gating on it or keeping it in memory (pins, token proofs, pool proofs, the head cross-check's memory, `light`'s seen anchor, names).

### The live run (D52)

`just e2e-lc-live` builds the release binaries (`scripts/release-check.sh`'s `cargo build --release` line) and the e2e debug binaries (the justfile's e2e lines), runs `./scripts/tor.sh`, refuses a binary older than HEAD's commit time (naming it), then `lkd-e2e --lc-live <tor> <release dir> <debug dir> <foundry> <root>`. `lkd-e2e --lc-survey <tor>` runs stage 1 alone. Per chain (`LKD_LIVE_CHAINS`, default `mainnet,sepolia`), each stage one deadline, no loop:

0. **Binaries.** RLIMIT_MEMLOCK's soft limit raised to its hard one; `<release dir>/lkd-keyd --check-mlock`; refused (this host's seccomp refuses `mlock`): the debug dir, with `lkd start --no-mlock`, the one development option allowed, on keyd only; every verdict line then says `debug build: this host refuses mlock`. Not a run.
1. **Preflight (the survey)** over a tor of the harness's own (the pinned bundle, its own SOCKS port in `TMPDIR`), with `curl --socks5-hostname` and `User-Agent: curl/8.23.0` (netd's): per suggested beacon source, the four light-client paths with `Accept: application/octet-stream` (`bootstrap` at the newest grid root, the root `blocks/{first slot of the current period}/root` names; `updates?start_period=<current>&count=1`; `finality_update`; `optimistic_update`), each its status and Content-Type (SSZ or JSON); then `finality_update` and `optimistic_update` as JSON for their fork names and attested slots, and `blocks/{finalized slot}/root`; per suggested EL endpoint, `eth_getProof` of anvil's #0 by `blockHash` at the finality update's attested and finalized execution blocks (ok, or the error's code and message). One `e2e lc-live survey <chain> <source>: …` line each, printed before the wallet starts (To confirm 6; 7 for Nimbus and Lodestar, the suggested sources serving Gloas).
2. `lkd init` (anvil's words, public endpoints over Tor, light client 1, the suggested sources, checkpoint at first start, `tor =`); `lkd start`: "<k> of <n> sources agree" with k ≥ 2 (each source that did not answer printed as a survey line), `yes`, unlock; each daemon's argv (`/proc/<pid>/cmdline`) carries no development option (`--no-mlock`, `--test-root`, `--tamper`, `--dev-`), but keyd's `--no-mlock` under stage 0's fallback.
3. The overview's "proved at block A, signed by s of 512 …; final up to F", s ≥ 342 (10 min).
4. On `lkd-lc.sock`, each answer re-checked as the UI does (`lkd_ui`'s re-checks): `Account`, `AccountFinal`, `Head(0)`, `Head(1)`, `BlockHash(A − 2, 0)`, `BlockHash(F, 1)`, every `Token(i, #0)`, `Pin(i)`, `Pool(i)`, `Included` of the first transaction of the newest block at or below A − 64 that has one (the oracle names it), and `lkd status`; values against the oracle's reads at the same block hashes (by `blockHash`, over the harness's tor); each `Pin`, `Token` and `Pool` verdict against the one recomputed from the oracle's reads at that hash (Keccak of `eth_getCode`, the implementation slot, the condition slots): equal and matched passes; equal and not matched is `table drift: <pin>` (reported, not failed); different fails.
5. Names and prices: mainnet's `lkd-ui ens vitalik.eth`, its primary name, `lkd-ui prices`, labelled as `LKD_LIVE_NAMES` says (`anchored`, the default: the anchored label; `endpoint`, `quorum` until 2026-10-28: "on one endpoint's word" with the not-proved line, for a no to D44 or a tree without lc9-ens).
6. **The request budget.** Over the first automatic refresh that starts after the session-start pin batch, the first snapshot pass and a cache commit have completed and more than a minute before the next pass, with no harness query outstanding: `lkd network traffic`, judged on the light client's classes only: beacon `GET`s on `Light(src)` (one `finality_update` a slot, every source once an epoch), `ElHeader` by hash and `HeaderAt` (one each per anchor), `ElProof` (one per address), `ElStorage` with D39's `History` reads (at most `ASKS`); every other class (the UI's `eth_chainId`, `aggregate3`'s `balanceOf`, the pending nonce, `eth_getCode`, prices, received-funds reads) printed, not judged. The snapshot pass measured once on its own against its own: one `ElHeader(F)`, one `ElProof` per address, the token reads, D47's name proofs (about 10, to the selected address's endpoint).

A stage that fails is probed at once: stage 3 each source's `finality_update` (its participation and age); stage 4 the same `eth_getProof` by `blockHash`; otherwise every request `lkd network traffic` lists as failed, denied or timed out in the stage's window, rebuilt from its method, host and shown bytes. Each probe goes through the wallet's tor (its SOCKS socket, `curl --proxy socks5h://localhost<socket>` with the user and password `isolation::password` gives the request's group and host on 443: the failed request's circuit while tor keeps it), else the harness's tor (said), with the wallet's deadline for its class (`curl --max-time` 8, 12 or 27); a third party's HTTP status (403, 429, 5xx) in netd's outcome that the probe reproduces counts as not answered; curl's TLS is not netd's, so a refusal by TLS fingerprint is not reproduced (said). `FAILED: <stage>: <why>` (the wallet's) when every probe is answered or no request failed; `inconclusive: <probe>: <error>` when any is not. Verdict lines `e2e lc-live <chain>: green|inconclusive: <why>|FAILED: <why>`, exit 0, 3 or 1. `LKD_LIVE_DIRECT=1` (the user's yes to D52) adds a direct-route run. `lc-live-dry` runs the same step functions hermetically on the development chain (public sources over the fake tor and TLS, anvil as the oracle, stage 5 on `place_ens` and `place_prices`) with the debug build.

### Invariants (LC9)

| Row | Owner | Review |
|---|---|---|
| 25o restated (`0x0f`, `0x10`, `0x8e`, `0x8f`, error 9) | lc9-wire | restated |
| 25q restated (`Started`, code 12); tested clause (`Started` sent, rounds, two-phase deadlines, the queued-in-netd rule, the 90 s precondition) | lc9-wire; lc9-deadlines | restated |
| 25r restated (dispatch, window failure); deadline clause | lc9-history; lc9-deadlines | restated |
| 25p restated (final answers); its UI clause (25y) | lc9-history; lc9-ui-a | restated |
| 25s: type 3 and the journal codec row; its UI clause (the records the UI writes, `record_account`, `record_tokens`, on a `Reaches` store's finalized header) | lc9-ens; lc9-ui-a | storage; restated |
| 25t's and 25u's UI clauses (pointing to 25y; D3's part to the Journal row) | lc9-ui-a | restated |
| 25x new after 25u (`Head`, `BlockHash`; key set 6 on `Shared`, routed by hash, tested); UI withdrawal clause (tested) | lc9-history; lc9-ui-b | spec |
| 25y new after 25x (the UI's halves: acceptance H_lc-free; composed) | lc9-ui-a | spec; storage and mixing for `record_*`, `included`, `pin`, `fresh`, `committee_size` |
| 25w restated (kernel proved: needs, table, freshness, the configured input; glue tested); Journal `Included` UI clause (keep rules proved, outcome 1 from `AccountFinal`) | lc9-ui-b | mixing; storage |
| 28h, 29g new (anchored names and prices: the reads, the root, the outcome table, `W`); 15j restated (the anchored lookup's reads before `y`) | lc9-ens | spec; 15j's second reviewer |
| 10i: D4's fallback note (base); key set 6 issued on `Shared` (proved group), routed by P's hash (tested) | base; lc9-history | egress |
| 26b new; group 25 sorted; the group's intro for LC7, LC8 phase 2, LC9; the Keccak-256 row (`LkdBase.KeccakFast`); this file's summary table | integration | |

### Tests (LC9)

Plan-test cases `LkdTests/Lc9/{History,Deadlines}.lean` (bounds and outcomes, never per-step fetch counts); Rust unit tests per module (the name facts' sizes from `crates/verified/tests/fixtures/mainnet/ens` beside a 27 KB update; netd's error mapping on reth's, geth's and 4444 replies, kept sanitized; the round rule; the shell's two phases and queued-in-netd rule; `keyd`'s retention with eight account records and two name records of one block; `pin_gate::light` and the UI's configured glue; freshness at the bound, past it, with a future timestamp and with the clock behind); Kani `lc_wire`, `lc_channel` at fixed lengths under a 16 GB cap; e2e `lc-proof-window` (lc9-wire), `lc-deadlines`, `lc-live-dry` (lc9-deadlines), `lc-final` (lc9-history), `lc-reorg` (EIP-2935's slot for N rewritten with another hash after a pin batch and the pools' line were proved at N, so `BlockHash(N, 0)` proves it and the UI withdraws them; the `History` reads on `Shared`, at most `ASKS` a refresh, none at an anchor an `Account` read used) and `lc-fail-closed` (a deposit typed without `LKD_SETTINGS` while netd runs with beacon sources and `lkd-lc` does not: blocked) (lc9-ui-b), `lc-names-anchored`, `lc-name-facts` (lc9-ens); `lkd-e2e --lc-survey` once in lc9-deadlines and once at the integration; `e2e-lc-live` once at the integration.

### Second reviewers (LC9)

Every restated statement (25o, 25q, 25r with `Routed`/`step_query`, 25p with `anchored_sound`'s hypothesis, 25s, 25t's and 25u's clauses, 25w, 15j, the journal rows) and 25x, 25y (`lean-gate` skipped); storage: type 3, D48's writer and its order against `keyd`'s retention, `inclusion_keep`, D7's outcome 1 from `AccountFinal`, `lc_check::record_account`, `record_tokens` and `included`; mixing: `pin_gate` with `needs` and the configured input (D60, netd's `Health.beacon`), D58's freshness and `lc_check::fresh`, `pin`, `committee_size`, `reorg`'s withdrawal in pins and pools (G14); egress (10i): key set 6's first issuance, its move to `Shared`, D39's numbers routed by hash; netd's rounds, `Started` and the own-node window mapping; D44's reads at a UI-named block and root, their routing by address, and the name rule in send reviews (the outcome table, `W`); the keccak port (`scripts/CheckCore.lean`'s rule 5, `LkdBase.KeccakFast`, the `ABORTS.allow` entry); `AGENTS.md`'s changed rules (D54, D57). The independent review pass of 2026-10-28 covered these too ([Second reviewers](#second-reviewers)); the human second reviewer is still owed.

### Tracks and what they own (LC9)

| Track | Branch | Owns | Posts | Waits |
|---|---|---|---|---|
| lc9-wire | `lc9/wire` | `Wire.lean` but namespace Snapshot; `Lc/Wire.lean`; `Lc/Core.lean`'s What decodes fits; `LkdTests/Lc6/Harness.lean`'s `describe`; `lc_wire.rs`, `lc_channel.rs`, `Refinement/{LcWire,LcChannel}.lean`; `lc.rs`'s client (`identity`, `Lc::head`, `Lc::block_hash`, `Lc::account_final`, `error_words`, `Unanchored`); netd `rpc.rs` `node_error`/`Failure::Pruned`, the `code()` functions of `lc.rs`, `lc_storage.rs`, `lc_bodies.rs`; `light.rs`'s Execution proofs row; `settings.rs`'s Where-the-wallet-reads notes; `doctor.rs` `proof_window`; e2e `proved.rs`'s Liar window modes, `lc9window.rs`; on a no to D59, `g12_endpoint`'s arm | WIRE_LEAN, WIRE_RS, WIRE_DONE | HEAD (part 2's e2e) |
| lc9-deadlines | `lc9/deadlines` | `Plan.lean`'s three constants, `PlanCommon.lean`'s `jobMs`/`bodyJobMs`; `deadlines.rs`, `Spec/Deadlines.lean`, `Refinement/Deadlines.lean`; plan and incl tests' expectations, `Lc9/Deadlines.lean`; `crates/lc` `shell.rs`, `oneshot.rs`, `channel.rs`, `tests/shell.rs`; netd `server.rs` `turn`, `lc.rs` `serve_one`/`answer`/constants, `tests/{lc,beacon,sandbox}.rs`; the UI's `TIMEOUT` line and windows' docs; e2e `live.rs`, `lc9deadlines.rs`, `Mode::{LcLive, LcSurvey}`; justfile `e2e-lc-live` | PLAN_CONSTS | WIRE_RS, HEAD (part 2) |
| lc9-history | `lc9/history` | `Lc.lean` `accountFinalLight` and the `Plan.want` call lines (makeSnapshot's included), `Storage.lean`'s `Plan.want` call, `Step.lean`, `Blocks.lean`; `Plan.lean` `want`/`fail`, `PlanStorage.lean`, `PlanIncl.lean` `fail`, `PlanCommon.lean` `Failure`; `LkdProofs/Lc/{Step,Anchored,Blocks,Plan (want, failures),PlanStorage,PlanIncl,StorageCore,InclCore}.lean`, `Lc/Core.lean`'s handler lemmas, `Lc/Storage.lean` but its record lemmas; `Lc9/History.lean`, `Lc6/Scenario.lean`'s AccountFinal line; `egress.rs` `keys_group`'s `History` arm, `Spec/Egress.lean`, `Refinement/Egress.lean` where key set 6's group shows; netd `lc_storage.rs` `endpoint_key`; `proved.rs` `final_account` and the settled lines, `history.rs` status; e2e `lc9history.rs` | HEAD, HISTORY_LEAN | PLAN_CONSTS, WIRE_LEAN, WIRE_RS, SNAPSHOT |
| lc9-ui-a | `lc9/ui-recheck` | `lc_check.rs`, `Spec/LcCheck.lean`, `Refinement/LcCheck.lean`, `Lc/Ui.lean`; re-check bodies in `lc.rs` (`Lc::head`'s and `Lc::account_final`'s in part 2), `pins.rs` `check_pin` and `Proved.timestamp`, `token_proofs.rs` `check_token`/`settle`, `pool_proofs.rs` `check`/`keys`/`head_of`/`names_the_pool`, `included.rs` `judge`, `snapshot.rs` `recheck`'s and `recheck_tokens`' bodies | LC_CHECK, UI_ACCEPTS, UI_COMPOSED | WIRE_RS, SNAPSHOT (part 2); HISTORY_LEAN, PIN_GATE (part 3) |
| lc9-ui-b | `lc9/ui-gates` | `pin_gate.rs`, `inclusion_keep.rs`, their `Spec`/`Refinement`; `pins.rs` `needs`/`bit`/`act`/`can_block`/`cause`/`gate`/`gate_over`/`settle`/`view`/`configured`/`lc_runs`/`prove`'s re-ask; `proved.rs` `crossed` and its memory; `included.rs` `decide`/`ranked`/`settled_by_nonce`/`shown`/`plausible`/`consumed`/`settled_record`; `reorg.rs` (the base's stub); `pool_proofs.rs` `checks`; `token_proofs.rs` and `light.rs` withdrawal; netproto `Health`'s `beacon`, netd `Upstream::health`'s; e2e `lc9reorg.rs` | PIN_GATE | LC_CHECK, HEAD (part 2) |
| lc9-ens | `lc9/ens` | netproto `0x21`–`0x23`, `0x95`; netd `reads.rs` At reads, `upstream.rs` `proved_*_at`, `server.rs` At arms; `names.rs`, `prices.rs`, their label sites and the review's name act (`tui.rs`, `main.rs`, `gui/src/view.rs`); `Wire.lean` namespace Snapshot, `Lc.lean` finalizer..checkSnapshot (not makeSnapshot's `Plan.want` line), `Lc/{SnapshotWire,Snapshot,SnapshotName,SnapshotToken}.lean`, `Lc/Core.lean`'s snapshot block (`verdicts_data` to `checkSnapshot_no_account`), `Lc/Storage.lean`'s record lemmas, `Refinement/Snapshot.lean`, `snapshot.rs` (verified; UI: the name-fact pass); `keyd` journal's retention test; e2e `lc9ens.rs`, `proved.rs`'s Liar At mode; `spec/17`, `spec/18`, `08`'s Snapshot row | SNAPSHOT | WIRE_RS, LC_CHECK (part 2), HEAD (part 3) |

### Working agreements (LC9)

LC7 and LC8's ([Working agreements](#working-agreements)), with SRC `track-lc9-base`, BASE `build/lc9-base`, the same lock scripts (`lc78-heavy.sh` `$H`, `lc78-e2e.sh` `$E`, `lc78-lc-check.sh`), cargo `$T/target-<id>` and charon `$T/target-<id>-charon` made by the base, and these changes: `CARGO_INCREMENTAL=0` everywhere (the base's target is warmed so and copied without `debug/incremental`); `df --output=avail -BG /projects` ≥ 25 G before each cargo, lake, kani or e2e step (else post and wait); **one `Funs` build at a time**: `Extraction/Funs.lean` peaks near 25 GB when it builds, so after every `just extract` the first build is `$F $H lake build LkdProofs.Extraction.Funs`, and `cargo kani` runs as `$F $H bash -c 'ulimit -v 16777216; cargo kani …'`; `$F` is `$T/lc9-funs.sh` (one machine-wide slot, `flock` on `$T/lc9-funs.lock`, the shape of `lc78-heavy.sh`), always taken before `$H`, never inside it; no `sorry` is ever committed (an unproved statement is left out, or kept as a documented `def …Statement : Prop`, and said in As built). Module declarations go where rustfmt sorts them (`reorder_modules`): `pub mod reorg;` between `receive` and `sandbox` in `crates/ui/src/lib.rs`; the e2e's `lc9deadlines`, `lc9ens`, `lc9history`, `lc9reorg`, `lc9window` after `lc8ui`, `live` between `ledger` and `pp`. Anvil (COORDINATION.md's lc7-core and lc7-tokens-ui notes): `anvil_setCode` and `anvil_setStorageAt` change the newest block's state in place, so after one, mine a block and ask until the answer's anchor is past it (`lc7::wait_past`); a slot written to zero stays an RLP(0) leaf, which `storageB` refuses; a chain on which anything is sent uses `no_mining`. A post is merged with `git merge --no-ff <sha>`, then extract (if `crates/verified` changed), the Funs build, the core static libraries and `touch` of the two `build.rs`. `WIRE_RS` is posted only once `Refinement.LcWire` and `LcChannel` build again, so every tree holding it builds whole; a tree holding `WIRE_LEAN` without `WIRE_RS` (lc9-history's) checks Lean with `lc78-lc-check.sh`. Posted names: BASE, WIRE_LEAN, WIRE_RS, WIRE_DONE, PLAN_CONSTS, HEAD, HISTORY_LEAN, SNAPSHOT, LC_CHECK, UI_ACCEPTS, UI_COMPOSED, PIN_GATE, ANSWERS, INT (a fix re-posted as WIRE_RS2 and so on). Never in a track: the full e2e suite, `check-kernel`, `release-check`, `lean-gate`, `just ci`, `e2e-lc-live`; the one real-network run in a track is lc9-deadlines' single `--lc-survey` (read-only, no wallet).

### The decision gate (LC9)

At BASE the orchestrator puts D39, D44, D45, D46, D47, D48, D49, D52, D53, D54, D55, D58, D59 and D60 to the user once, each with its default and cost, and posts ANSWERS; tracks build answers given, defaults otherwise; the fast-forward of `feat/light-client` waits for every answer and for the user's word on the live verdicts; a no reverts its `(Dn)` commits or swaps its constant or arm and reruns the targeted checks (a no to D44 or D47 starts the deferred follow-up after LC9; D49's line level a later track; a yes to D55 a follow-up on `AccountFinal`; D53 and D54 change only the docs pass's text; a no to D52 leaves the live run to the user; a no to D59 is lc9-wire's arm, or the integration's after lc9-wire's done line).

**The user's answers (2026-10-27, `ANSWERS`)**, posted before the tracks' part 2, so every track built them; no `(Dn)` commit was reverted and no constant swapped:

- **D39** yes: `reorg::ASKS` = 4, up to two `History` proofs per shown pin or pool batch block, on `Shared`.
- **D44** yes: ENS and prices read at the anchor in the UI (`At` reads), in place of the deferred `lc9/quorum-pins`; key-set tags 8 and 9 and query `0x0e` stay reserved.
- **D45** yes: names wait like shared reads (`names::WAIT_SHARED`).
- **D46**: a typed acknowledgment, `names::UNANCHORED_SEND = Act::Ack`.
- **D47** yes: the UI's type-3 name facts, in place of the deferred `lc9/ens-facts`.
- **D48** yes: the selected account's primary name, its reads routed to that address's endpoint, `snapshot::NAMES = 1`.
- **D49**: the value level (the line level a later track's).
- **D52** as designed: both chains over Tor, read-only, the debug build with keyd's `--no-mlock` on this host, which refuses `mlock`; the release run is the user's, on a host that locks memory.
- **D53**: not the default: public beacon sources on a route to your own node only after an explicit opt-in with the notice (open decision 9, option (b), built by `lc9/own-node`).
- **D54**: described in `AGENTS.md` as practice, not a rule.
- **D55**: not in LC9; the received-funds notice is listed for later.
- **D58** yes: `gate_bound_s` 768 s on mainnet and Sepolia, 90 s on the development chain.
- **D59** yes: the fallback within a session too, as built (no `(D59)` commit).
- **D60** yes: fail closed for a command `lkd` did not start.

### As built (LC9)

#### lc9-wire
LC9's frames in Lean and Rust with their refinements, the UI's client, and "your node refuses
proofs at block N" (`lc9/wire`; posts WIRE_LEAN `e1583646`, WIRE_RS `5943fa70`, WIRE_DONE
`e1a2af3c`).

- **Frames** (`LkdLc.Wire`, `lkd_verified::lc_wire` and `lc_channel`, as LC9's Frames give
  them): the queries `BlockHash(n, final)` (`0x0f`) and `Head(final)` (`0x10`), the answers
  `BlockHash` (`0x8e`) and `Head` (`0x8f`) with `BlockHashCert` (an absent part empty) and their
  values (`BlockHashAnswer.ok`, `HeadAnswer.ok`; Rust `block_hash_ok`, `head_ok`, rule for rule),
  error 9 `NodeWindow`, the reply `Started` (`0x83`, 13 bytes) and code 12 `Window`. Every match
  on them has its arm: the core answers the new queries `Unsupported` until lc9-history routes
  them; `lkd-lc`'s shell and the one-shot root read skip `Started`, the fetch still in flight,
  until lc9-deadlines' two-phase deadline takes it.
- **Proved** (25o, 25q restated): the general round trips, canonicity, injectivity, caps and
  what-decodes-is-wf cover the new frames, each answer through its own parser
  (`parseBlockHash_bytes`, `parseHead_bytes`, `parseBlockHash_wf`, `parseHead_wf`), and a
  handler's check before it answers is the frame's (`Lc.fitsBlockHash_wf`, `fitsHead_wf`); one
  example per frame (`layout_blockHashQuery` to `layout_nodeWindow`, `Channel.layout_started`,
  `layout_window`), the bodies `body_blockHash` and `body_head`, `Channel.replyBytes_started`.
  Refined with no precondition added (`fits` bounds each new answer's byte strings at 2^20 bytes,
  as LC7's): `parse_query_lc9_spec`, `parse_answer_lc9_spec`, `parse_block_hash_spec`,
  `parse_head_spec`, `put_block_hash_spec`, `put_head_spec`, `block_hash_ok_spec`, `head_ok_spec`
  and the injectivity of the new values; `Refinement.Snapshot`, `Journal` and `Cache` build
  again. Kani (16 GB): `decode_encode_lc9_query`, `parse_block_hash_total`, `parse_head_total`
  (frames of their fixed part and up to 4 bytes more), `decode_encode_reply` with `Started`;
  the harnesses that reach the changed decoders ran again and pass.
- **The UI's client** (`lkd_ui::lc`): `Lc::head` (the header under the anchor's hash at its
  number, final as asked), `Lc::block_hash` (re-checked by its callers), `Lc::account_final`
  (anchored, marked final, at the finalized block only; `Lc::account` refuses an answer marked
  final). lc9-ui-a rewires their re-checks to `lc_check`.
- **The node's proof window** (D42; [The node's proof window](#the-nodes-proof-window)): netd's
  `rpc::Failure::Pruned` on the light client's `eth_getProof` by hash, `Window` from your own
  node (`lc::served_code`, `lc_storage::served_code`), `Node` otherwise; the UI's
  `Unanchored::Window(Option<u64>)`, `error_words(9)` and `window_words`, the block named from
  `Head` at most once a slot (`HEADS`) and kept for the thread that read it (`refused_at`);
  Settings' Execution proofs row (`window_refusal`); Where the wallet reads worded per
  configuration (with a light client: what is proved at its anchor, "a node that lies
  consistently is believed" said of the quorum path only); `lkd doctor`'s reth line with the
  finalized block's depth. Tested: `rpc::tests` (reth's, geth's, 4444 on a proof and on
  receipts, a public endpoint's refusal, an OSC 52 payload kept unprintable), `lc::tests`,
  `lc_storage::tests`, `lc_bodies::tests`, the UI's `lc::tests` (the anchor's block, F for the
  final reads, `Head` asked once a slot, Settings' row cleared by a read answered), `doctor`.
- D59 answered yes: `Upstream::g12_endpoint` keeps its fallback within a session (no commit).
- **e2e `lc-proof-window`** (`crates/e2e/src/lc9window.rs`, on HEAD `3de4d13b` merged): the
  Liar (`proved.rs`, `refuse_proofs`) plays a node's proof window `W`, refusing `eth_getProof` at
  a block hash more than `W` blocks behind the head as reth does (`-32602`) or as geth does
  (`-32000`, "missing trie node <root> (path )"); proofs at a block number, netd's own reads of
  the newest block, pass. The head is taken one past anvil's newest block: the fake beacon
  attests anvil's newest block at the next slot, where a real chain's tip has moved on, so
  `W = 0` refuses the anchor as reth's default window does. On an own-node chain, the chain held
  once the anchor is the newest block: with `W = 0` the overview's balance and `lkd balance` say
  "not anchored: your node refuses proofs at block N …", N the anchor `Head(0)` names, Settings'
  Execution proofs row says it, and a Tornado deposit's review is blocked naming it, `y` signing
  nothing; geth's refusal once says the same; with `W = 1` the balances stay anchored and green
  at the anchor while `AccountFinal` (`proved::final_account`), the snapshot pass
  (`snapshot::make`, which Settings' row says) and G12's final proof (`lkd status` of a
  transaction below F) say "… at block F". On public endpoints (a second wallet, `node = public`,
  three endpoints and the beacon source behind the fake tor, its salt sending anvil #0's proofs
  first to a refusing endpoint) the next endpoint anchors the balance, with no word of a window.
  Run once with `lc-anchored-cli`, `lc-tokens`, `lc-own`, `lc-tokens-ui`, `lc-settings-cli` and
  `lkd-settings`: each passed on its first run; `lc-proof-window` named the anchor's block 63 at
  `W = 0`, kept the anchor 64 green and named F 63 at `W = 1`, and on public endpoints
  `rpc2.test` refused 8 proofs while the next endpoint anchored the balance.
#### lc9-deadlines
Built on `lc9/deadlines` (2026-10-27), in three parts.

**Part 1.** `lkd_verified::deadlines` (`crates/verified/src/deadlines.rs`, the Aeneas subset): the
constants of [The deadline model (D43)](#the-deadline-model-d43) (`BEACON_MS` 8000, `EL_MS` 12000,
`BODY_MS` 27000, `MARGIN_MS` 3000, `QUEUE_LIMIT_MS` 120000, `CORE_MARGIN_MS` 5000, `JOB_MS` 140000,
`BODY_JOB_MS` 155000, `UI_FRAME_MS` 10000, `UI_NETD_TIMEOUT_MS` 40000) and `service_ms(kind)`
(`0x13`, `0x14` a body's, `0x20` to `0x24` a beacon request's, the rest an EL one's), specified in
`Spec.Deadlines` and refined in `Refinement.Deadlines` (`constants_spec`, `service_ms_spec`,
`jobMs_eq`, `fetchMs_eq`, `bodyJobMs_eq`, `shell_within_core` and `netd_within_shell` by
`decide +kernel` over the 256 kinds, plain `decide` hitting `maxRecDepth`, `service_ms_within_core`,
`page_within_core`, `ui_within_timeout`, `isBody_kindOf`, `shell_within_job`; Audit
`[lc9-deadlines]`). The planner (7676dca2): `maxJobs` 2, `perStep` 2, `maxStorageWithBody` 1,
`jobMs` 140 s, `bodyJobMs` 155 s; `LkdProofs.Lc.Plan` needed no repair; `Lc6/Plumbing.lean`'s
body-rule checks now ask `Plan.Plan.mayAsk` (two in flight pre-empt it in `issue`) and check
that no fetch passes `maxJobs`; `Lc7/Cases`, `Incl/Cases` and `Incl/Job` pass unchanged;
`LkdTests/Lc9/Deadlines.lean` on G12's mainnet world: at most two fetches in flight, a user read
asked before a batch's next storage fetch, a body beside at most one storage fetch, G12's job run
to its end, the bounds after every input (PLAN_CONSTS 4c60bfc6). netd's rounds (d86881e7,
a7c29cf5): `Server::turn` keeps the round under way (connection ids) and whether a datagram is
due after it; `server::tests` show a datagram served after at most one round while frames keep
coming and a waiting frame after at most one datagram; `tests/lc.rs`'s `a_ui_frame_goes_first`
is now `frames_and_datagrams_take_rounds`. The live run's harness (a5368173, e54ce4d8 (D52),
eaa25dee, d127f41f): `crates/e2e/src/live.rs`, `Mode::LcLive` and `Mode::LcSurvey`, the justfile's
`e2e-lc-live`, `lc-live-dry`. As built, `e2e-lc-live` refuses a binary older than the newest
commit of its sources (`git log -1 -- crates proofs/core`), not HEAD's commit time: a binary
cargo found fresh is as old as its last build, older than any later commit that touched no
source, and could never pass. Shared one-liners: `lkd-netproto` in `crates/e2e/Cargo.toml` (netd's
traffic entries by type), `pub beacon` on `lc6::Following` (the dry run stops a source).

**The survey** (2026-10-27, read-only, over a tor of the harness's own in its `TMPDIR`; run once,
and once more after the fix that reads a Gloas header's `execution_block_hash`), one line per
suggested source:

- mainnet `lodestar-mainnet.chainsafe.io`: the bootstrap at grid slot 15523840, the period's
  update, `finality_update` and `optimistic_update` all 200 in SSZ (fulu); serves the four paths
  in SSZ. `ethereum-beacon-api.publicnode.com`: the four 200 in JSON only (netd re-encodes
  Electra and Fulu). `http://testing.mainnet.beacon-api.nimbus.team`: the four in SSZ. The EL
  endpoints `eth.drpc.org`, `0xrpc.io/eth`, `rpc.mevblocker.io`: `eth_getProof` by `blockHash` at
  the finality update's attested (26285186) and finalized (26285120) blocks, ok: each proves by
  block hash.
- Sepolia `beacon.sepolia.ethpandaops.io/nimbus`: the four in SSZ (gloas).
  `lodestar-sepolia.chainsafe.io`: the bootstrap at grid slot 11444224 refused (500), the other
  three in SSZ (gloas): does not serve that bootstrap. The EL endpoints
  `rpc.sepolia.ethpandaops.io`, `0xrpc.io/sep`, `eth-sepolia.api.onfinality.io/public`: ok by
  `blockHash` at the Gloas headers' `execution_block_hash` (the parent payload's).

**Part 2a.** Merge of WIRE_RS 5943fa70 (11b2cfd3, clean). netd's `Started` (b26ecb94):
`lc::Channel::answer` sends it under the fetch's generation and tag right before serving a decoded
`Fetch`, never for a `FetchPage` or a datagram that does not decode, dropped when it would block
(`Channel::started`); `EL_DEADLINE`, `BODY_DEADLINE` and `BEACON_DEADLINE` come from
`lkd_verified::deadlines` (values unchanged; `LONGEST_DEADLINE` stays, `lc8ui.rs` reads it);
`tests/lc.rs`, `beacon.rs` and `sandbox.rs` read past `Started`. The shell (431ed324): `shell::Flights`,
given the instant by its caller, holds each fetch's phase: due 120 s after its sending, then
`started_deadline(kind)` after its first `Started` (11, 15 or 30 s), a page 123 s after its
sending; the queued-in-netd rule `MAX_QUEUED` 2 (sent and not started; a fetch timed out
unstarted counted until any reply for its tag, `Started` included, or `STALE_FOR`, 240 s, after
its sending; pages neither counted nor refused; restated by the integration's review fix: a
`Started` for it no longer ends its count, its page or failure does, or the later of
`STALE_FOR` and its kind's service and the margin after that `Started`), a refused fetch told `NotSent` at once;
`Started` never reaches the core; one standard-error line per `TimedOut` (`timed_out_line`:
`lkd-lc: TimedOut: <kind> fetch <tag>: not started by netd within 120 s`, `...: started by netd,
not answered within <n> s of it`, `lkd-lc: TimedOut: FetchPage of fetch <tag>: not answered
within 123 s`); `fetch_deadline` and the old per-kind constants are gone, and so are lc9-wire's
forced arms; the one-shot's `ask_roots` waits each `BlockRoot` in the same two phases
(`ask_roots_in`), its 60 s window unchanged. `Flights` and `Flight` are public so that
`tests/shell.rs` drives the rules at exact instants; the binary builds them only inside the
`Shell`. "Queued in netd" is built as worded: a fetch in flight netd is serving when another is
sent does not count (its own deadline bounds it, and the planner's `maxJobs` holds the next);
one that timed out unstarted, which the core has forgotten, counts while netd serves it (the
review fix above). The UI (1423d579): `netd::TIMEOUT` from `UI_NETD_TIMEOUT_MS`; `ANSWER_WITHIN`,
`PIN_BATCH_WITHIN`, `MAKE_WITHIN`, `INCLUDED_WITHIN` and `POOL_WITHIN` keep their values, their
docs calling them budgets. The live run's stage 4 (c0dbe6cd) asks `AccountFinal`, `Head(0)`,
`Head(1)`, `BlockHash(A − 2, 0)` and `BlockHash(F, 1)` (WIRE_RS's client), re-checking a block
hash's certificate with `recheck_storage` against EIP-2935's account and slot (this tree has no
`lc_check::history_hash`).

**Part 2b.** Merge of HEAD 3de4d13b (6f12338f, clean; extract, the Funs build, the core static
libraries). `lc-deadlines` (b94507e, `crates/e2e/src/lc9deadlines.rs`, the scenario's module doc
for its steps), on the development chain behind lc8ui's `Gate`, which is made public and gains
`hold_each` (every request a rule takes held, not only the first) and `release`, its other uses
unchanged. Its run of 2026-10-27: (a) G12's receipts held 20 s at the node: the UI's pin batch
answered 20.4 s after they were held, every pin matched, the token batch 20.6 s after, every token
matched, `lkd balance` in 21.0 s (within the UI's 40 s), G12 then proving the transfer; a Tornado
deposit's review then not blocked ("code pinned, proved at block 83"); (b) for 30 s, 247 refreshes
(the longest 1.2 s), 1,497 pin batches and 616 name lookups, each answered: the UI frames netd
served between a fetch's sending and its `Started` at most 1.4 s over 51 fetches; (c) the lookup
with its three proofs held 9 s each answered in 27.1 s, and a pin batch asked meanwhile completed
27.3 s after the first proof was held, every pin matched, none timed out; no `TimedOut` line in the
session. The measurement reads netd's traffic, which netd serves one request at a time: for each
of the light client's fetches (a beacon `GET`, or an EL read naming a block hash) the UI's
requests between it and the fetch two before it, which had started when it was sent (the
queued-in-netd rule); a fetch whose block hash netd's shown bytes cut off counts as the UI's,
which only adds. In that run (c)'s traffic was taken from the lookup on, so no fetch preceded its
frame and (c)'s line read 1 ms; it is now taken before the chain moves on to (c)'s anchor
(`a_long_frame_counts_for_the_fetches_behind_it`), not run again in this track (the three-run
cap). (b) and (c) hold the chain still: in (b)'s second run, the chain moving, one of its name
lookups was refused, "malformed ENS proofs the state root does not accept", a proof read at the
newest block not holding under its header's root, as when anvil serves the newest block's state
while it mines the next one (not shown further); the UI's quorum reads are all at the newest
block, and a real chain's blocks do not change.

`lc-live-dry` ran three times (its fixes 9ef7b56). Its first run passed vacuously: the fake tor took only netd's SOCKS
greeting (`5 1 2`), so curl's (no authentication, then username and password) was refused and
every survey line and the probe said "No authentication method was acceptable"; the fake tor now
takes username and password among the methods offered, as tor does, and the dry run checks that
each fake source serves the four paths in SSZ and that the probe meets the stopped source's 500
again through the wallet's tor (both held in its second run). Its second run showed stage 6's
window spanning 0 s: from one `ElProof` of anvil's #0 to the next, which one refresh makes at two
anchors, and the UI's own account proofs at a number counted as `ElProof`. Now the window runs to
the first proof a refresh later (20 s, the terminal UI's `POLL`), `ElProof` counts per address and
anchor, and an `eth_getProof` is the light client's only when it names a block hash (or, cut short
in netd's shown bytes, is about a pinned contract or EIP-2935's). Its third run then measured a
real refresh, 31 s, and failed on the budget's formula, 36 `finality_update`s against 35: every
source once an epoch was counted once, while a refresh spans five of the development chain's 8 s
epochs. The formula now counts each epoch the window touches (`Net::spanned`,
`a_refresh_spans_slots_and_epochs`: 32 + 3 × 5 = 47 for that window); not run again in this
track (the three-run cap): the integration's verification runs it.

**Timings.** As D43 decided, a fetch netd never started times out 120 s after its sending (48 to
67 s before), a page 123 s (40 s before), and a third fetch while two are queued in netd hears
`NotSent` at once, which the planner counts as an attempt and LC1's quorum path caches as
`Unreachable`. `lc-quorum`, `lc-netd-restart`, `lc-killed-mid-page`, `lc-killed-mid-body`,
`lc-netd-busy` and `lc-pins` passed on their first run with their bounds unchanged
(`lc-netd-busy`'s broadcast 15.0 s and receipt poll 14.5 s behind receipts held 15 s;
`lc-killed-mid-body`'s `lkd balance` 4.1 s and `lkd status` 2.0 s).

**For a second reviewer** (D43): netd's rounds (`server.rs` `turn`), its `Started`
(`lc.rs` `answer`, `started`), and the shell's two phases and queued-in-netd rule (`shell.rs`
`Flights`), all tested, not proved.
#### lc9-history
Part 1 (`lc9/history`, 2026-10-27). `Lc.accountFinalLight` answers `AccountFinal(a)` at the
store's finalized header F as `accountLight` answers `Account(a)` at the anchor: `finalAnswer`
(F's EL header bound by 25j, the proof by 25k, anchor ⟨number, F's EL hash, the anchor's signers,
the committee's size⟩, `anchoredFields s l st F true`, `fitsAnchored`), `NotAnchored`, the read's
error, `Refused`, `Pending` as `accountLight`; `step` routes it (`Lc9Query`, `Routed`; `step_query`
restated with one disjunct for LC9's handlers, which `Head` and `BlockHash` join in part 2, so
the other users of `step_query`, `Lc/Evidence.lean` and `Lc/Snapshot.lean`, gained one case each).
`finalAnswer` also keeps an answer only when its finalized EL number is its own block's:
`finalizedNumber_bind` shows it is for a Gloas-form or `Own`-tagged F, and the case left, a
payload-form F at a Gloas slot, which `Store.isValidHeader` refuses at its slot's fork on every
table, is not excluded for an arbitrary `Chain`, so the check makes `anchoredFinal_sound` hold
without an assumption on the table. `Plan.want now named h fin a p` keeps the account reads and
the EL headers at every hash the context names (callers pass `(ctxOf s l).named`, or `Storage`'s
`named st L`). `anchored_sound` gains `hx : x.isFinal = false`; `anchored_final_iff` and
`anchoredFinal_sound` as stated above, over `AnchorProved`, moved from `Lc/Storage.lean` to
`Lc/Anchored.lean` (its Audit line kept). Egress: key set 6 on `Shared` (`keys_group`,
`keysGroup`; `publicGroup_head` and `storageByHash_group` restated; `history_shared`). The
`Lc6/Scenario.lean` check that said `AccountFinal` was unsupported now asks it and gets `Pending`
(its anchored final answer came with the plan test, part 2a).

Part 2a (`lc9/history`, 2026-10-27; PLAN_CONSTS 4c60bfc6 and WIRE_LEAN e1583646 merged).
**Tests**: `LkdTests.Lc9.History`, in `lkd-lc-plan-test`: `AccountFinal` answered final at block 1,
its finalized number its own; `Account`, `AccountFinal` and `MakeSnapshot` asked in turn, then
served: each answered at its own block, both reads held; `Head` and `BlockHash` below; the
`Lc6/Scenario.lean` check moves the own world's chain on until block 1 is finalized and gets the
anchored final answer there. **`LkdLc.Blocks`**: `headLight` (P the anchor's attested header for
`Head(false)`, the finalized header for `Head(true)`; the answer once the planner holds P's EL
header bound to P, `fitsHead`; else the header's error while it is told, else `Pending` with the
header wanted on its own; a header held that makes no answer `Refused`, dropped) and
`blockHashLight` (P likewise; ahead and too old at once from P's EL number, `Included.elNumber`;
at P's number, P's own EL hash with its header alone; otherwise a `PlanStorage` read of
`History(n)` at P's EL hash through `Storage.respond`, answered when `Inclusion.hashOf` of the held
proof gives a hash, else `Refused`); `step` routes both (`Lc9Query`'s and `Routed`'s new cases).
**The planner**: `Plan.wantHeader` (an EL header wanted on its own: no read, no poll held back)
and `Plan.headerError` (a header given up, told `Unreachable` for `errorMs`: the planner keeps
when its asks gave up, not why); `readCands` asks every named EL header the planner keeps an entry
for until it is held or given up (before, only while some account read, or a storage read or G12's
job at that hash, wanted one); `PlanStorage.keysOf (.history n)` derives EIP-2935's contract and
`Pins.historySlot n`, and a storage read made from its hash alone has the key set
`HistoryFor(0, [])`, which `keysOf` never derives (the plumbing test unchanged). **The window**
(D42): `Plan.Failure.window`, lcproto's `NodeWindow` (9); `Plan.fail` (`ElProof`),
`PlanStorage.fail` (`ElStorage`) and `PlanIncl.fail` (G12's history proof, `Job.stop`) end the read
at once on the channel's `Window` (12); tested in `LkdTests.Lc9.History` (one ask, where another
failure is asked three times). **Proofs**: `LkdProofs.Lc.BlocksCore` (the handlers' contract),
`LkdProofs.Lc.Blocks` (`head_sound`, `blockHash_sound`, `blockHash_status`, as stated above, the
last for any state), `Lc.step_lc9`; `Lc9Answer` gains `Head` and `BlockHash`,
`accountFinalLight_kinds` is new; every lemma enumerating failures gains the window's case. Tested
on G12's mainnet world: `BlockHash(N, 0)` proved by the fixture's EIP-2935 proof, its certificate
re-checked as the UI does. **netd**: `lc_storage::endpoint_key` sends `History(n)` to the endpoint
the block hash picks (`history_by_the_block_hash`). `crates/lc-core/tests/steps.rs`'s timeout
check reads `deadlines::JOB_MS`: D43 moved `Lc.fetchMs` from 57 s to 140 s. Not yet built:
`proved::final_account` and G11's lines, `lc-final`, and `steps.rs` asking LC9's new queries
without a light client (their Rust frames come with WIRE_RS).

Part 2b (`lc9/history`, 2026-10-27; WIRE_RS 5943fa70 merged; HEAD). `crates/lc-core/tests/steps.rs`
asks `Head` and `BlockHash`, final and not, of a core with no light client: `Unsupported`, as
`AccountFinal`. **`lkd_ui::proved::final_account(netd, chain, address) -> Result<Final,
Unanchored>`** (D40): `Lc::account_final` (anchored, marked final, at the finalized block itself;
asked again after each `Pending` for at most `ANSWER_WITHIN`), then `Head(true)` at the same block
for F's header's timestamp (`lc::Proved` carries no timestamp in this tree; lc9-ui-a's
`Proved.timestamp` is the same header's once merged, and the `Head(true)` ask can go), then
`cross_check_block(F, F's hash, F)`: agreement, or a verifier disagreement (noted for the
overview), never "your node disagrees", since F is final; unanswered, `Cross::Unchecked`, asked
again at the next call. `Final {nonce, balance, block, hash, timestamp, signers, of, crossed}`. An
accepted answer is kept by its address with its F and given again until an epoch of the chain has
passed since it was asked (half `light::fresh_ms`: 384 s on mainnet and Sepolia, 8 s on the
development chain); a refusal, an error or no answer is not kept, so D7's one ask a transaction is
never answered from an earlier failure (`lkd-lc` tells a failed read's error for `errorMs` before
reading again); with `lkd`'s settings configuring no light client, `NoCheckpoint` without asking.
Unit tests against a fake `lkd-lc` and netd: the answer kept for an epoch and asked again after
it; `Pending` waited for; an error, or `Head(true)` at another block (F moved between the two
asks), kept nothing; the cross-check asked again while unanswered; another header at F a
disagreement. **`lc-final`, its lcproto part** (`crates/e2e/src/lc9history.rs`): on a chain
following the fake beacon with EIP-2935 planted and automine off, once F is past the chain's first
blocks and the chain held, `final_account` of anvil's #0 at F (`cast`'s nonce and balance there,
F's hash and timestamp, 2/3 of 32 signing, cross-checked agreeing); `Head(0)` and `Head(1)`,
anvil's blocks; `BlockHash(F, 1)` by F's header alone; `BlockHash(A - 1, 0)` by one history read at
A's hash, which the node sees, its certificate checked again (A's header, the history contract's
pinned code, the slot's value); `BlockHash(A + 5, 0)` ahead, nothing read. On your node every
request is netd's `Own` group, so the scenario sees the history read at A's hash, not its group:
key set 6 on `Shared` is proved (`history_shared`) and its routing by hash tested in netd. Not
yet built: G11's lines and `lc-final`'s UI half (part 3).

Part 2c (`lc9/history`, 2026-10-27; SNAPSHOT e257aac9 and `lc9/wire` 8c50174e, which holds
WIRE_DONE e1a2af3c, merged; HISTORY_LEAN). Both merges were clean but for `spec/INVARIANTS.md`,
resolved row by row: 25o and 25q are lc9-wire's restated rows, 25p keeps this track's final
answers. No statement changed: over lc9-ens's name facts (`Record.names`, `verdicts`' fifth
argument, `recordOk` refusing names) and lc9-wire's frame lemmas, `anchored_sound` (with `hx`),
`anchored_final_iff`, `anchoredFinal_sound`, `head_sound`, `blockHash_sound`, `blockHash_status`,
the handlers' `good`, `moves` and `kinds`, `want_bounded`, `step_query`, the window's failure
lemmas and egress's `publicGroup_head`, `storageByHash_group` and `history_shared` build as they
were, none with `sorry` (`lake build`; `check-axioms.sh`; `check-core.sh`: 26 abort sites, none
new), and `lkd-lc-plan-test` passes its 482 checks.

Part 3 (`lc9/history`, 2026-10-27; no Lean and no `crates/verified` changed since HISTORY_LEAN).
**G11's "settled at block F, final"** (D40). `proved::at_final` takes `final_account`'s answer for
G11's lines: the nonce at F once F's cross-check agrees (`AtFinal::Proved`; an unchecked F adds
nothing, and `final_account` asks the cross-check again at the next call), `AtFinal::Not` for your
own node's refusal of the proof at F (`Unanchored::Window`, lc9-wire's words) and for a
disagreement at F, nothing for the rest. `proved::nonce_line(n, p, fin)` says "Nonce n: settled at
block F, final (proved nonce p); inclusion not proved yet" once the nonce at F is past `n`, else
the head's line, with "; not final: …" for `AtFinal::Not`; `may_replace`, `settled_refusal` and
the freshness labels keep the head's proof. `history::Next` gains `at_final` and
`Status::Settled` its `finality` (`history::Finality`: `Unsaid`, `Final`, its block and nonce
then F's, `Not(why)`): "settled by nonce at block F, final (proved nonce p), inclusion unproved";
a receipt for it or its nonce's others, and a record D7 kept, still come first; the nonce at F
settles a transaction whose head proof failed too; `lkd history --json` keeps its keys, its
`block` F. The TUI asks off the screen's thread: at a refresh's end `App::ask_final` names each
address of the account in use with a transaction its head's nonce settles and F does not yet, and
one thread at a time calls `final_account` for each (kept for an epoch: an address is read at most
once an epoch), its news (`Event::Final`) read by the transaction screen, and so the window's,
and through `App::next_nonce` by the History screen and Home's Recent; a final once shown stays
final, whatever a later answer that proves nothing says (`App::final_news`). `lkd history` asks
`final_account` for each address with such a transaction before it prints. Tested:
`proved::tests::settled_lines_say_final_at_f`, `history::tests::settled_at_f_is_final`,
`tui::tests::a_settled_transaction_is_final_at_f`. **`lc-final`'s UI half**: on the same chain,
the wallet on a nonce ledger of its own, a transfer from the TUI replaced outside `lkd` at its
nonce while the chain is held, the replacement mined in a block R of its own, the light client's
head, which no finalized block reaches while held: its screen says "settled at block R (proved
nonce n + 1)", not final, with no speed-up or cancel; the chain moving again, "settled at block F,
final (proved nonce p)", F at or past R and p `cast`'s nonce at F. Not seen there: the History
reads on `Shared`, since on your own node every request is netd's `Own` group; key set 6 on
`Shared` is proved (`history_shared`) and its routing by P's hash tested in netd
(`history_by_the_block_hash`). Run once, each passed: `lc-anchored-cli`, `lc-snapshot`,
`lc-mined-ui` (its D7 record still reads "settled by nonce at finalized block F"), `lc-final`
(replaced at nonce 0 in block 54, settled there, then final at F 54, proved nonce 1) and
`settled-nonce` (no light client: the head's line, unchanged); `final_news`'s keep rule came after
that build, and `a_settled_transaction_is_final_at_f` covers it.
#### lc9-ui-a
Part 1, LC_CHECK (`lc9/ui-recheck`; the acceptance theorems, the refinement and the composed
theorems are parts 2 and 3).

- **`lkd_verified::lc_check`** (extracted; `crates/verified/src/lc_check.rs`): field-free
  `Refusal`; `committee_size` (512 on 1 and 11155111, 32 on 31337, else 0); `identity_ok`,
  `anchored_ok` (its `of` must be the chain's committee size: the answer's own `of` no longer
  sets the two thirds, D50), `header_at`; `account` (kind 2, final exactly as asked: an answer
  whose final flag is not the query's is refused, `Anchor`) and `account_endpoint` (LC1's kind 1);
  `slots` (a `StorageCert`) and `words` (a `PoolCert`); `pin`, `token` and `pool`, each reading
  its row from the chain's table for the index (and owner) asked; `token_balance`
  (`pins::balance`, `settle`'s pure part); `history_hash` (the proving header's own hash at its
  number; else EIP-2935's slot under its state root, the contract's code `HISTORY_CODE`, the
  value nonzero), `inclusion` (the verdict and certificate) and `included`; `head` (an `Agreed`,
  an `Anchored` and the header's bytes, no `lc_wire` answer type); `record_account` and
  `record_tokens`; `GATE_BOUND_S` 768, `GATE_BOUND_DEV_S` 90, `gate_bound_s`, `fresh` (D58, its
  own commit). Every accepted result carries the re-checked header's number, hash and timestamp.
  Aeneas's subset shaped it: each slot's read is a function of its own (`value_read`; matching
  on `mpt::storage` of a slot's field inside the loop failed Aeneas's join), `header_at` and
  `head` take `rlp` (a parameter named `header` shadows Lean's `header` namespace in the
  extraction), and `pins::same32`'s loop is copied (it is private).
- **The UI** calls it: `lc::check` (both kinds), `check_identity`, `check_anchor`,
  `recheck_storage`, `recheck_included`, `pins::check_pin`, `token_proofs::check_token` and
  `settle`'s balance, `pool_proofs::check`, `included::judge`, `snapshot::recheck` and
  `recheck_tokens`; `lc::Refusal::of` words the kernel's refusals and adds a `Chain` refusal's
  numbers. Signatures are kept but `check_anchor`'s, which gains the chain the committee size
  comes from (the e2e's two callers, `lc7.rs` and `lc8.rs`, pass the development chain). A row
  passed to `check_pin` or `check_token` is the table's, which the kernel reads itself.
  `recheck_included` refuses (`History`) a history pair other than EIP-2935's as `lc_check` pins
  it. `pool_proofs`' `keys`, `head_of` and `names_the_pool` moved into the kernel (`head_of` now
  maps its `Pool` to `Head`); `included`'s `history_code` is gone. `lc::Proved`,
  `pins::Proved`, `token_proofs::{Proved, Checked}` and `pool_proofs::Proof` gain `timestamp`.
  `lc-anchored-cli`'s stand-in (`crates/e2e/src/lc6.rs`) answered on the development chain as
  signed by 498 of 512, which D50 now refuses: it signs as 31 of 32.
- **`LkdProofs.Spec.LcCheck`**: each check's definition, taking what was asked, over
  `Spec.Header.verify`, `Spec.Mpt`'s readers and `LkdLc.Pins`, in the code's structure;
  `Accepted` with `accepted_iff`; `historyCode_eq` (the pinned code hash is Keccak-256 of
  `LkdLc.El.History.code`, by `decide +kernel`).
- **Checked**: `just extract`; the `Funs` build; `lake build` (3839 jobs, no `sorry`); nightly
  `fmt --check`; `clippy -p lkd-verified -p lkd-ui -p lkd-gui -p lkd-e2e --all-targets`;
  `cargo test -p lkd-verified` (every test passed; `lc_check`'s are 13) and `-p lkd-ui
  --test-threads=1` (186 passed); the track's e2e, `lc-anchored-cli` (after its stand-in's
  fix), `lc-tampered-answer`, `proved-balances`, `lc-tokens-ui`, `lc-pools-ui`, `lc-mined-ui`,
  `lc-snapshot` and `lc-cli`, each passed.

Part 2, UI_ACCEPTS (`lc9/ui-recheck` after merging WIRE_RS `5943fa70` and SNAPSHOT `e257aac9`;
the end of the track's Rust).

- **The merges.** WIRE_RS's `Lc::head` and `Lc::account_final` called the re-check helpers part 1
  replaced, so the merge rewired them (step 4): `Head(final)` through `lc_check::head`,
  `AccountFinal` through `lc_check::account` with the final flag asked; each refuses what it
  refused, with the chain's committee size in place of the answer's `of` (D50). lc9-wire's tests
  of both named 400 of 512 signers on the development chain; they name 31 of its 32 (21 for the
  too-few case). With SNAPSHOT's `Record.names`, `record_head`, which `record_account` and
  `record_tokens` share, takes one account fact and no name fact (else `Fields`), and
  `Spec.LcCheck.recordHead` says `r.names.length = 0`: `snapshot::recheck` and `recheck_tokens`
  refuse a record with a name fact, as SNAPSHOT's UI test asks. That is `lc_check`'s one API
  change at UI_ACCEPTS.
- **The acceptance theorems** (`Spec.LcCheck`, H_lc-free, 25y): `account_accepts` (kind 2, the
  final flag as asked), `accountFinal_accepts` (its finalized block the one read),
  `accountEndpoint_accepts` (LC1's kind 1), `pin_accepts`, `token_accepts` and
  `token_balance_accepts`, `pool_accepts`, `blockHash_accepts` (`history_hash`),
  `included_accepts`, `head_accepts`, `recordAccount_accepts`, `recordTokens_accepts`. Each names
  the inputs the UI asked, each equal to the answer's (but `blockHash_accepts`: `history_hash`
  takes the block and final flag asked, and its caller compares them with the answer's, with the
  identity and the anchor), and every result field the UI shows,
  gates on or keeps, in the terms of `lkd-lc`'s halves, so that part 3 composes them:
  `Lc.SlotsRead` and `Lc.WordsRead` (`slotsCode_ok`, `wordsCode_ok`), `Lc.slotValues`,
  `Lc.TokenHolds` (`tokenFactOk_holds`; `recordTokens_accepts` concludes what
  `Lc.tokenRecord_sound` does of each token fact, and the indices increasing), and
  `LkdLc.El.History.blockHash` (`historyHolds_iff`, for the 32-byte hashes the UI passes).
  `token_accepts` is the statement above with the certificate's header as its bytes
  (`.data.toList`), the word the balance slot's value (a number), and the verdict's byte and
  detail the answer's. `Spec.LcCheck` imports `LkdProofs.Lc.Storage` for those definitions.
- **The refinement** (`Refinement.LcCheck`): every public function of `lc_check` computes its
  `Spec.LcCheck` definition on every input with no precondition (so none panics); the helpers
  with the preconditions their callers establish (one slot per key, a byte range within the
  word); the loops by invariants over the prefix read so far (`slot_values`, `word_values`,
  `token_slot_values`: the first failure; `slot_words`, `token_slot_words`: the values from a
  place on; `zeros`, `be`; `token_facts`: what is still held, with the facts from a place on).
  `lc_check`'s copies of `pins::same32`, `same20` and `low20` are `pins`' own, by unfolding;
  `pool_keys`' test that the head value fits 64 bits is redundant (`rootSlot_large`: no layout's
  root slot takes a larger one). `account_accepted` to `record_tokens_accepted`: an `Ok` the code
  returns is a result the specification accepts, so the acceptance theorems hold of it.
- **Docs**: `INVARIANTS.md` 25y new (after 25u, where lc9-history's 25x goes; the integration
  sorts group 25), 25p's UI clause (`Ui.balance_line_sound` restated as `Ui.account_sound`), 25s's
  (the records the UI writes; their header the finalized one of a `Reaches` store is `lkd-lc`'s
  word, composed in part 3), 25t's and 25u's (pointing to 25y; D3's part to lc9-ui-b's Journal
  row); `Audit.lean` `[lc9-ui-a]`; this file's composed theorems (As built, LC9) and Tested, not
  proved.
- **For the second reviewers**: the new 25y statements and the restated 25p, 25s, 25t and 25u
  clauses (`lean-gate` not run); storage: `lc_check::record_account` and `record_tokens` (the
  name-fact refusal new here), `included`, `inclusion`, `history_hash` with `HISTORY_CODE`;
  mixing: `pin`, `fresh`, `committee_size`.
- **Checked**, each once and passed on its first run: `just extract` (after the merges; the
  Rust has not changed since); the `Funs` build; the four core static libraries;
  `lake build` (3841 jobs, no `sorry`); `check-axioms.sh` ("axiom check passed"); nightly
  `fmt --check`; `clippy -p lkd-verified -p lkd-ui -p lkd-gui -p lkd-e2e --all-targets`
  with `-D warnings`; `cargo test -p lkd-verified` (every test; `lc_check`'s 13, the record
  test now with a name fact) and `-p lkd-ui --test-threads=1` (188 and 2); the track's e2e,
  `lc-anchored-cli`, `lc-tampered-answer`, `proved-balances`, `lc-tokens-ui`, `lc-pools-ui`,
  `lc-mined-ui`, `lc-snapshot` and `lc-cli`, all passed in one run (9 min).

Part 3, UI_COMPOSED (`lc9/ui-recheck` after merging HISTORY_LEAN `6758b099` and PIN_GATE
`c502cce0`; Lean only, no Rust change of its own).

- **The merges.** HISTORY_LEAN: `INVARIANTS.md` conflicted only where both added rows, 25x and 25y
  after 25u (both kept, 25x first) and 25p (lc9-history's final-answers clause and this track's
  UI clause, both kept). lc9-wire's window tests, which it brings, answer on mainnet with the
  test helper's anchor, which since D50 names the development chain's committee of 32: their
  mainnet answer now names 498 of 512, else `lc_check` refuses it (in the merge commit). PIN_GATE:
  the import blocks of `included.rs`, `pins.rs` and `proved.rs` conflicted, each side having
  dropped what its own rewiring stopped using; the merge keeps what the merged code calls.
- **`LkdProofs.Lc.Ui`** (imported after `Refinement.LcCheck`): `Ui.account_sound`,
  `accountFinal_sound`, `accountEndpoint_sound`, `token_sound`, `pin_sound`, `pool_sound`,
  `included_sound`, `head_sound`, `blockHash_sound`, `record_sound`, `tokenRecord_sound`,
  `settled_sound` and `gate_pass_sound`, the pairs of the composed theorems' table above, every
  one proved, on the standard axioms. The glue: `bind_verify` (what `Anchor.bind` keeps is what
  `Spec.Header.verify` reads from the same bytes under the beacon header's EL hash), so the
  UI's header and `lkd-lc`'s are one; `accepted_config` (`Configured`); `agreed_eq`;
  `verify_keccak` (a record's header is under its own hash, so the record's hash is the finalized
  header's EL hash). For the gate: `PinSeen` (what the UI holds of a need's pin: the answer, the
  accepted result, the cross-check, the gates), `foundOf` (the verdict without its detail),
  `causeOf` with `causeOf_matched` (matched exactly when the accepted verdict is matched, the
  cross-check agrees and D58's freshness holds), `verdict_code`, `pinOf_pinned`.
- **What they say beyond the halves.** The chain the UI asked is `lkd-lc`'s and its checkpoint, when
  it has one, the one the run starts from, rather than a hypothesis (`hcp` in the design's
  template). `Ui.included_sound` is for a proved verdict, the one `lkd-lc`'s half covers;
  `Ui.blockHash_sound` re-checks the block the UI passes (`n`) while `lkd-lc`'s half speaks of the
  answer's block, which is `n` when the answer replied to the UI's query (H_lc); the identity and
  anchor of a `BlockHash` answer are its caller's to check (`reorg::judge`, lc9-ui-b: the
  identity and the anchor by `lc_check::identity_ok` and `anchored_ok`, the answer's block the
  one asked, not final). The integration's review fix takes those checks as `Ui.blockHash_sound`'s
  hypotheses (`hok`, `hasked`: glue, tested), so that it concludes `Configured`, `Replies` for
  the `BlockHash(n, isFinal)` the UI asked and `P` by the asked flag, as the other pairs do.
  `Ui.token_sound` names H_6780 for a token behind a proxy (its verdict does not read the
  implementation's code; a `Pin` answer does). The records: their header the finalized one of a
  store `Reaches` gives, not an `AnchorProved` anchor (`record_sound` needs the configured chain id
  within 8 bytes, as `Lc.record_sound` does).
- **Not built**: `Ui.name_sound` and `Ui.prices_sound` (`Head`'s root with `Spec.Ens` and
  `Spec.Prices`, as time allowed).
- **Docs**: `INVARIANTS.md` 25y's composed clause, its theorems and status; `Audit.lean`
  `[lc9-ui-a]` (16 lines); this file's composed theorems (As built, part 3) and Tested, not
  proved.
- **For the second reviewer** (spec review: a wrong spec proves the wrong thing): each `Ui.*`
  statement and docstring, and 25y's composed clause (`lean-gate` not run).
- **Checked**: `just extract` after the merges (`crates/verified` gained `deadlines`, `pin_gate`
  and `inclusion_keep`); the `Funs` build (1797 jobs); the four core static libraries;
  `lake build LkdProofs` (3851 jobs, no `sorry`); `lake build LkdProofs.Lc.Ui`;
  `check-axioms.sh` (5012 reports, "axiom check passed"; the `Ui.*` theorems on `propext`,
  `Classical.choice` and `Quot.sound`). The merges' Rust, untouched by part 3 but for the one
  test: nightly `fmt --check` and `clippy -p lkd-verified -p lkd-ui -p lkd-gui -p lkd-e2e
  --all-targets` with `-D warnings` passed; `cargo test -p lkd-ui --test-threads=1` refused
  lc9-wire's two window tests on its first run, as above, then passed (194 and 2) at each merge.
#### lc9-ui-b

Branch `lc9/ui-gates` off BASE 1081229d, PIN_GATE c502cce0 posted after part 1; part 2 merged
LC_CHECK2 6bcfc6db and HEAD 3de4d13b (`git merge --no-ff`, then extract, the `Funs` build and
the core static libraries). Mixing review: the gate kernel with `needs` and the configured input,
D58's freshness, the withdrawal in pins and pools; storage review: `inclusion_keep`, D7's outcome 1
from `AccountFinal`.

- **The kernels** (aef7be38, c60e64f4): `lkd_verified::pin_gate` (field-free `Flow`, the target
  passed beside it; `Act` with `rank`; `Cause`, `Found`, `Seen`, `Crossed`; `Need {pin: u8 (255
  not pinned), primary, used}`; `needs`, `bit`, `act`, `can_block`, `checking`, `cause`,
  `combine`, `settle`, `crossed`, `light` with `LIGHT_*`, `CONFIGURED_*`, `SOCKET_*`) and
  `lkd_verified::inclusion_keep` (`Verdict`, `Learned`, `Shown`, `KEPT_NONE`, `PLAUSIBLE_AFTER`;
  `keep`, `settled_keep`, `plausible`, `ranked`, `settled_by_nonce`, `shown`), each `pub fn`
  refined on every input (`Refinement.PinGate`, `Refinement.InclusionKeep`) against
  `Spec.PinGate` (D1's table by `decide`; `needs` per flow against `LkdLc.Pins`, `uses_flat` by
  `decide` over every chain's table; `combine_pass_iff`, `act_block_funds`, `checking_wait`,
  `cause_matched`, `settle_matched`, `light_none`, `light_up`) and `Spec.InclusionKeep` (the keep
  rules' implications, `settledKeep_iff`, `ranked_proved`); 66 `#print axioms` lines in
  `Audit.lean`'s `[lc9-ui-b]` block. The UI calls them with its signatures and words unchanged
  (c502cce0).
- **D58** (3a0a8cf6): `pins::Clock` (the UI's clock and `lkd-lc`'s last phase 6 as `behind`,
  `Clock::fresh` = `lc_check::fresh` with `gate_bound_s`); the batch keeps each pin as the head
  cross-check settles it (`settle`, fresh as proved), and the gate settles it again through the
  kernel at each evaluation (`as_of`, `gate_at`, `gate_over_at`): a stale matched pin is
  "proved at block N, <age> ago: not proved now" (and "(your clock is behind the chain)" in phase
  6), so its age is the age now. `pins::reask` (called by the TUI's `pins_due` before each draw)
  asks the review's batch again only once `light::seen`'s anchor is past the stale pins' block.
  `pool_proofs::checks` counts a proof as "the pool knows it" only while fresh (`rooted`; else
  the node's word, `Rooted::Word(Some(Why::Stale {..}))`, the flow checking its tree as without a
  light client); a token send's gate takes the rule through `gate_over` (`W` only). Labels keep
  F's display rule.
- **D60** (b09691aa, 94d0df0f): netproto `Health.beacon` (1 byte after the route; codec, the
  truncation test's offsets), filled by `Upstream::health` with the beacon sources netd was
  started with. `pins::configured(netd)`: `lkd`'s settings when passed, else `Health.beacon`
  (`configured_of`: 0 none, else sources only, netd silent sources only); `socket_of(&Status)`
  (`NotFound` missing, any other error silent, running from a zero checkpoint, running; `Pending`,
  an error code or another chain count as running, their words then the batch's); `light` the
  kernel's verdict in words. `view` returns no light client only when the configured input alone
  says none (it never probes the socket at each draw), the batch (`prove_at`) decides the rest
  through `light`; `token_proofs::prove` and the token gate take the same verdict. `lc_runs` is
  gone. The TUI's withdrawal test now runs with a netd that says it runs no beacon source
  (e87c50cf): without settings and with no netd the input fails closed.
- **D7** (2c0b9264): `included::run`'s `Ask::Settle` asks `proved::final_account`, and
  `consumed(&Result<Final, Unanchored>, n)` keeps outcome 1 through `settled_keep` with the real
  acceptance (an `Ok` answer, `lc_check::account` final at F) and F's cross-check (agrees);
  the record names the configured checkpoint, else the one `lkd-lc` was last seen running from
  (`current_checkpoint`). `MakeSnapshot` is no longer asked for it.
- **D39** (8d780dd6, 57178965, 975e6990, cfc3cce3, 7abcd73d): `lkd_ui::reorg` keeps the base's API
  (`ASKS` 4, `note`, `replaced`) and adds `batch` (D39's "last batches": `Batch::Pins` for a pin
  batch's blocks, `Batch::Pool(i)` for pool `i`'s last proof, each in place of the last batch of
  its kind; `note` stays for a value shown on its own, kept until both its asks are made), `seen`
  (the free check), `check` and `line`. `batch` is called by `pins::prove_at` with the blocks of
  its re-checked answers and by `pool_proofs::ask` with each proof's; `seen` by the head
  cross-check (`proved::cross_check_block`, `CrossChecks::block`), which every
  anchored answer goes through (balances, tokens, pins, pools, inclusion, `final_account`, names);
  its memory is the last `proved::CROSSED_KEPT` anchored blocks; the older of two hashes at one
  number is the one replaced, and an answer at a block already replaced changes nothing. `check`
  runs at each refresh's end on a thread of its own (`App::check_reorg`, one at a time, an
  `Event::Reorg` drawing the screen again): the due blocks at `light::seen`'s anchor (at least
  N + 2 not asked yet, or N final not asked since), `proved::wait_shared()`, then **only when
  `lkd-lc`'s anchor (`Head(false)`, waited for while it fetches the header the asks read anyway)
  is a block none of the UI's answers named** (`unused`: not the last `Account` reads' anchor,
  none of the anchored blocks the free check saw; D37's wait is a time, and on the development
  chain the mover mines a block every three slots), at most `ASKS`, newest first,
  `pins::ask_all` within `included::INCLUDED_WITHIN`; each answer `judge`d (identity, anchor not
  final, the block asked, `history_hash` under the anchored header; too old only by the numbers),
  one ask covering both when N is already final. Withdrawn: `pins::withdrawn` (in `as_of` and
  Settings' row; `reask` also asks a batch holding a replaced pin), `token_proofs::read_of` and
  `implementation_code`, `pool_proofs::rooted` (`Why::Replaced`) and `Rooted::text`
  ("withdrawn"), `proved::kept` (the entry dropped), `light::seen` (`Anchored` gains the block's
  `hash`; the anchor hidden while replaced). The yellow line in the overview (`light_lines`), the
  window's alerts (`scene_of`) and `lkd balance`, until a batch notes a block at M or past it.
  LC1's differential (`App::ask_lc`, the address in use asked of `lkd-lc` again after each
  refresh) now counts as an `Account` read: its anchored answer calls `proved::note_accounts`
  (D37's wait, for pin batches and pool syncs too) and `reorg::seen` (7abcd73d); it went out at a
  new anchor when the anchor moved after the refresh, which nothing else knew of.
- **e2e** (`crates/e2e/src/lc9reorg.rs`, `[lc9-ui-b]`): `lc-reorg` and `lc-fail-closed`, as the
  module says. The harness routes EL reads to your own node, where netd keeps every request in
  `own`: the history reads are checked to ride no address's circuit, `Shared` being egress's group
  for key set 6 at a public endpoint (lc9-history's `history_shared`). Runs (`$E`, each scenario
  at most three times): `lc-fail-closed`, `lc-mined-ui` (D7 from `AccountFinal`: "settled by nonce
  at finalized block 70"), `settled-nonce` passed; `lc-tokens-ui`, `lc-pools-ui`, `shield` and
  `privacy-pools` failed once with netd not coming up under the machine's load (a netd started by
  hand then came up at once) and passed on their rerun; **`lc-reorg` did not pass in this track**:
  run 1 never saw block N replaced (every batch's blocks stayed noted, and an explicit refresh's
  newer ones took the four asks: D39's "last batches", cfc3cce3; the scenario now waits for the
  automatic refresh); run 2 found it replaced, withdrawn and proved again, and failed on its own
  traffic check (the route's group, the pins' read of the history contract taken for a history
  read: 17892067); run 3 passed those and found one history read at the block hash of the Account
  read just before it, LC1's differential at a newer anchor (fixed in 7abcd73d, unit-tested, not
  run again: the three-run cap). Its D58 half (the stale review) has not run yet: the integration
  runs `lc-reorg` (verification step 10). After 7abcd73d, which the refresh of every TUI
  scenario runs, the seven others ran once more in one `$E` run and all passed, and
  `Refinement.PinGate` and `Refinement.InclusionKeep` build against the merged extraction.
  `lc-pools-ui`'s commands run on a netd started without beacon sources: their reviews now say
  "code not checked: no light client" (D60); the scenario checks the roots, which still come
  from `lkd-lc`.
- **For the integration**: `included.rs`'s D7 test no longer builds a `MakeSnapshot` record, to
  which lc9-ens and lc9-history added `names: Vec::new()`: take this side. `tui.rs` holds the
  re-ask in `pins_due`, `check_reorg` and its call in `refreshed`, `Event::Reorg` and the line in
  `light_lines` (the track's shared edit was the line alone: the check has to run at a refresh,
  and the re-ask before a draw). Tested, not proved (the integration's docs pass): D1's kernel with
  `needs`, the configured input and freshness, D3's and D7's keep rules and the cross-check verdict
  are proved; the gate's glue (the target is the transaction's `to`; the configured input from
  `lkd`'s settings or netd's `Health`; the socket from `Lc::status`; the UI's clock and `lkd-lc`'s
  phase as freshness reads them), the stale re-ask and G9's withdrawal are tested.
#### lc9-ens
Part 1 (`lc9/ens`, 2026-10-27; posted as SNAPSHOT e257aac9). **netproto**: requests `0x21`
`ProvedNameAt { at, via, name }`, `0x22` `ProvedReverseAt { at, address }`, `0x23`
`ProvedPricesAt { at }` (`at` netproto's `At`: a number and a state root) and the reply `0x95`
`Parts`, with round trips and refusals. **netd**: `reads::{name, reverse, prices}` take a block
(number, state root) in place of a head; `Upstream::{proved_name_at, proved_reverse_at,
proved_prices_at}` agree on no head and read today's `EnsProof` and `PriceProof` at the number
asked, each part checked under the root asked; the reverse read and a nonzero `via` go first to
the endpoint `el_endpoint(address, 0)` picks, a typed name and the prices in turn
(`at_reads_go_first_where_the_address_reads_go`); `server.rs`'s At arms answer `Parts`.
**Fact type 3**: `LkdLc.Wire.Snapshot.{NamePart, NameFact}`, `Record.names` (default `[]`),
`maxKeys` 10, the list and `ByteArray` codecs (`parseNames`, `parseParts`, `parseKeys`) with their
round trips and canonicity; `Lc.partHeld`, `Lc.nameHeld`, and `verdicts` over the account, token
and name facts (`checkRecord` counting all three); `LkdProofs.Lc.SnapshotName`'s
`partHeld_iff`, `nameHeld_iff` and `snapshot_name_held` (25s's held statement for a name fact);
`snapshot_held`'s, `record_sound`'s and `tokenRecord_sound`'s statements for types 1 and 2
unchanged (`Record.wf` counts names; `recordOk` also asks no names). Rust `snapshot::{NameSlot,
NamePart, NameFact}` and `Record.names`, refined (`Refinement.Snapshot`; `Refinement.Journal`
builds); every `Record` literal in the workspace gained `names: Vec::new()`; the UI's
`snapshot::recheck` refuses a record with names. `keyd`: a block's eight account records written
after its two name records are the ones kept (`a_blocks_account_records_outlive_its_name_records`).
Audit `[lc9-ens]` (79 theorems); INVARIANTS 25s (type 3) and the journal codec row.

Part 2 (2026-10-27; WIRE_RS 5943fa70 and LC_CHECK2 6bcfc6db merged). **D44**: `names::anchor`
(a light client configured as `proved::anchored` decides it, `lkd`'s settings else `lkd-lc`'s
`Status`; `Head(false)` asked again while `Pending`, up to `ANCHOR_WITHIN`, re-checked by
`Lc::head`, i.e. `lc_check::head`), `names::{forward_at, primary_at, cross}` and `prices::at`
with the outcome table, `names::Provenance` kept in `Named`, `Primary` and `Names` (an anchored
entry hidden once `reorg::replaced`), `Prices.provenance`; the UI's netd client
`proved_{name,reverse,prices}_at`; label sites: the terminal's review line (coloured) and
Accounts, the window's Home, accounts, the send review's ENS field and Worth's level, the
history's labels, `lkd ens`, `lkd prices`, `lkd balance`'s values; the terminal reads prices on
a thread of their own (`Event::Prices`). **D58**: the anchored header counts only while
`lc_check::fresh` holds against `gate_bound_s`, the clock-behind flag from `light::seen` after a
fresh `Status`. **D45**: `names::WAIT_SHARED = true` (prices always wait). **D46**:
`names::{UNANCHORED_SEND = Act::Ack, send_act, send_reason, review_gate}`; the terminal's
`App::{review_gate, review_named, name_asks, keyd_warned}` feed `warned`, the pin hold, the
review's lines and the window's lead and alert; on the command line `confirm_name` asks a typed
`anyway` after the flow's gate (send, `--token`, `--stealth`, unshield, `pp withdraw`), `--yes`
refused. 15j restated.

Part 3 (2026-10-27; HEAD 3de4d13b merged). **D47**: `snapshot::name_facts` keeps a primary name
as two facts only when `ens::primary` gives it back to the address from netd's parts under F's
root and time, each part the read `ens` makes (`forward_reads`, `reverse_reads`,
`resolver_part`: the record version and a long name's words from the proved first keys) with the
keys `ens::read_slots` derives, their values and proofs; `snapshot::with_name` reads them after
`proved::wait_shared()` with `ProvedReverseAt` and `ProvedNameAt` via the address at the pass's
block (the header `lc_check::header_at` binds in its first record), `split` puts each in a record
of its own first, a fact that does not fit is not kept (`TOO_LARGE`, said on the saved line);
`newest` reads the names of the newest block whose records hold any (a pass at exit reads none),
rebuilds both facts from their own proofs under the record's root and time and compares them
(`recheck_name`), and `apply` keeps a name while both its verdicts do, at the lesser one; the
snapshot's line says a name dropped. Measured beside a 27 KiB update (the unit test, mainnet's
fixtures): vitalik.eth's reverse record (through the 2017 registry) 50,191 bytes, its forward
record 57,935, jefflau.eth's wrapped forward record 64,640, of 65,535. **D48**:
`snapshot::NAMES = 1`; `App::name_of` (the address in use, among the pass's anchored
addresses, on mainnet or the development chain); `write_snapshot` writes the name records
first; the overview gains a line under the address with its primary name (`App::name_line`),
the name read this session with how it was proved, else the snapshot's "(snapshot at block F,
…)" in the cached style; Accounts and the window's Home and rows fall back to it
(`App::shown_name`). **A fix the e2e found** (D44): a primary name read on the quorum path
while a light client is configured, as at a session's start before `lkd-lc` anchored, kept its
yellow line all session; `names::Names::due` reads it again an epoch later (384 s on mainnet
and Sepolia, 8 s on the development chain), at most eight at a time as before. **e2e**
(`crates/e2e/src/lc9ens.rs`): `lc-names-anchored` and
`lc-name-facts` as Tests (LC9) lists them, on a Following chain with ENS, the prices and a
primary name for anvil's #0 placed; the Liar's At mode (`proved::lie_at`: the account proof of
every `eth_getProof` answer at a given number altered), the anchor parted from the quorum's head
by mining one block while the beacon is held. **Docs**: [`17-ens.md`](17-ens.md) (at the anchor,
the outcome table, the routing, as facts, what is proved and trusted, Deferred), `18-prices.md`,
`08-accounts-journal.md`'s `Snapshot` row and retention, this file's overrides (snapshot
records, open decision 25, G19's rows, D5's and D25/D32's rows, What the UI trusts, the
compromised `lkd-lc` row and the colluding quorum), INVARIANTS 28h and 29g (new).

**Tested, not proved**: the anchored lookup's glue (which header and when, the outcome table, the
fallback's words), the routing by address (netd's unit test; the e2e runs on your node, the one
endpoint, where every request is on `own`), `W` and the review's stricter act, the name facts'
writer, its order before the account records, their rebuilding on load and their display.
`Ui.name_sound` and `Ui.prices_sound` (25y's "as time allows") are not built. **Open, for the
integration**: whether a light client is configured for names and prices follows
`proved::anchored`'s rule, not D60's `Health.beacon` (lc9-ui-b's): a command typed without
`LKD_SETTINGS` while `lkd-lc` is down shows names on today's path, with no `W`.

**Part 3's checks** (each once unless noted; logs in `/tmp/lt-lc9-ens`): after the merge, extract,
the Funs build and the core static libraries; nightly `fmt --check`; clippy on netproto, netd,
verified, ui, gui, keyd and e2e (`--all-targets`, `-D warnings`): run 1 two `similar_names` in
`lc9ens.rs`, run 2 passed, run 3 after the re-read fix passed; `cargo test` of netproto, netd,
verified, keyd and gui passed; lkd-ui's (`--test-threads=1`) 200 + 2, and after the re-read fix
201 + 2. **e2e**: run 1 (ens, prices, lc-snapshot, intent-order and the two new scenarios):
intent-order and lc-snapshot passed, then lc-names-anchored failed on a check of its own (on
your node every request is on `own`, so the circuit it looked for is not there) and the run
stopped; run 2 failed at the overview's own name, read before the light client anchored and
never again (the UI fix above); run 3 passed every check of lc-names-anchored (the anchored
labels, the expired name refused at the anchor and read at its number only, the altered proofs'
quorum path and `W`, the stale anchor's `W`, `lkd-lc` stopped: the review's `[W]`), then failed
leaving the cancelled review, one Esc short (fixed in the scenario, not run again: its three runs
spent); run 4, the scenarios no run had reached: lc-name-facts ("the first pass kept lkd-own.eth
as two facts at block 62, journal records [0, 1] before the account records from 2, held by
CheckSnapshot; started again with lkd-lc stopped, the name shown from the snapshot, then read on
the quorum path, not proved at the anchor"), ens and prices passed.

#### lc9-own-node

Open decision 9 as the user answered it on 2026-10-27 (LC9's D53: "opt-in on own-node routes"),
built on `lc9/own-node` off BASE in `crates/launch` alone (no Lean, no extraction). Decision 9's
row in the open decisions is this track's and stays as written.

- **`lkd init`'s fourth question** (`init::light_client`, `light_client_sources`,
  `sources_menu`, `own_node_yes`, `light_client_sources_after_menu`). On a public route
  (`Node::Public`) word for word as before, "1) public beacon endpoints, over Tor (recommended)".
  On a route to your own node (`Node::Ipc`, `Node::Tcp`, `Node::Onion`, hybrid or not) the
  opening drops its "Beacon endpoints see over Tor…" sentence and the menu starts with the
  notice: "Your node is your own: here public beacon endpoints are an opt-in. With them, tor
  starts unless the wallet runs it already, and the beacon endpoints see when an lkd light client
  is online, never your addresses: about 7,200 small polls a day while the wallet runs."
  (`init::OWN_NODE_NOTICE`; with `beacon_route = direct`, which only `lkd settings` sets,
  `OWN_NODE_NOTICE_DIRECT`: directly from this IP, seen by the beacon endpoints, your DNS resolver
  and your network). The three choices keep their numbers, none recommended: 1 "public beacon
  endpoints, over Tor: you confirm it next", 2 your own beacon node (refused over IPC, as
  before), 3 "no light client: balances and nonces are proved at your node's block, as before"
  (in hybrid mode "at a public endpoint's head", "at the block the public endpoints agree on"
  until 2026-10-28). Choosing 1 says the notice again
  and asks "Use public beacon endpoints? [y/N]"; Enter alone or no answers "Public beacon
  endpoints not taken: choose again." and asks the choice again; only a yes goes on to the
  suggested sources and the checkpoint.
- **`lkd settings`**: Light client → Beacon sources calls the same `light_client_sources` with
  the configuration's node, public endpoints and beacon route, so the same notice and yes;
  choosing your own beacon node or none removes public sources with nothing new asked. The one
  path that passes no menu, public beacon sources chosen on a public route and kept when Where the
  wallet reads (or the window's Networks form) moves the route to your own node, is said in the
  review before its yes (`settings::beacons_said`, shared by `lkd settings` and the window):
  "Public beacon sources kept on a route to your own node, where they are an opt-in: <the
  notice>. lkd settings → Light client removes them."
- **Not changed**: a public route's menu, review and labels; `lkd doctor`; the UI's Settings;
  `lkd start`, which runs a configuration as written, so one made before this change with public
  beacon sources on your own node's route, chosen under the old "(recommended)", keeps them until
  the user removes them.
- **Tests**: `init::Ask` reads a boxed `BufRead`, so tests script the answers (`Ask::script`,
  test-only). In `init`: `own_node_routes_take_public_beacon_sources_only_after_a_yes` (IPC, TCP
  and onion: Enter, `n`, `no` and `N` leave them out and ask again, no answer takes nothing, a yes
  takes the suggested ones on either beacon route, a no then a yes),
  `public_routes_take_public_beacon_sources_as_before` (no yes asked),
  `own_beacon_node_and_none_ask_nothing_new`,
  `the_menu_recommends_public_beacon_sources_on_public_routes_only` (the public menu byte for
  byte, each own-node menu whole, hybrid's and the direct route's lines),
  `step_four_on_a_route_to_your_own_node` (none asks no checkpoint, a yes goes on to it); in
  `settings`: `own_node_routes_add_public_beacon_sources_only_after_a_yes`,
  `beacon_sources_kept_on_a_move_to_your_own_node_are_said`. No end-to-end scenario answers the
  menu on a route to your own node (the anvil scenarios get no fourth question, and the
  real-network `--public` mode answers it on a public route, unchanged), so none changed.
- **Checks**: nightly `fmt --check`, `cargo clippy -p lkd-launch --all-targets -- -D warnings`
  and `cargo test -p lkd-launch` (40 passed) ran twice, the second after the notice's wording was
  tightened, both green; e2e `lc-settings-cli` and `launcher` (with `launcher-refusals`) passed
  on their one run (debug build, keyd with `--no-mlock`: this kernel refuses `mlock`).
- Not done here: the open decisions' row 2 (default sources), the docs pass's ("Sources,
  configured" now names both Sepolia sources `lkd init` suggests, ethPandaOps' Nimbus route and
  Lodestar's, as `init::SUGGESTED_BEACON` holds them); the README's step 4, which says what
  `lkd init` offers but not that it is an opt-in on your own node's route.

#### The integration

`build/lc9-integrate` off BASE (`1081229d`), merged `--no-ff` in this order, each conflict
resolved by the rules of the integration (rows by `rowmerge`, unions where both sides added):

- **master** `a6ffd225` (`7751bf50`): the withdrawal-proof and spending-cap fix, public endpoints
  by default, the wallet set up in windows, the keymap fix, the JSON-RPC id fix (this line's
  `2214badf`, so netd's `rpc.rs` keeps this line's text) and `perf/keccak-csimp`, ported to this
  line's layout: `LkdCore/KeccakFast.lean` moved to `LkdBase/KeccakFast.lean`, imported by
  `LkdBase.Common`, `LkdLc.El.Trie` and `LkdCore.Eip1559`, so `lkd-lc`'s header, trie and
  storage checks run it too; master's `proofs/core/CheckCore.lean` deleted and its rule
  (readable Keccak-256 called only in its own module) made rule 5 of `scripts/CheckCore.lean` for
  every runtime library (a probe without `Trie`'s import fails it); `Lanes.digest`'s
  capacity-32 buffer in `ABORTS.allow`; master's 19c and 19h numbered 27c and 27h as this line
  numbers `keyd`'s rows. Master's first run in windows builds a `Config`, which here has a light
  section: none of its questions is the light client's, so it gets no beacon source (Settings
  adds them) and the install's random salt, as `lkd init` gives every install. G12's whole job
  on the kept blocks fell from 268.6 ms (mainnet) and 267.4 ms (Sepolia) at LC7 and LC8 to
  10.8 ms and 10.5 ms (`lkd-lc-incl-test --budget`, the verification's run).
- **lc9/wire** `6de1eefd` (`70f06e9c`), **lc9/history** `5d296cab` (`7d537ac1`): clean.
- **lc9/deadlines** `a273193b` (`e2e633bd`): 25q, a row with two clause owners, merged from its
  text (lc9-wire's frames clause and lc9-deadlines' tested clause, each whole).
- **lc9/ens** `6c30666e` (`6d8c7e76`): the e2e Liar keeps both modes (the proof window and the
  reads at a named number).
- **lc9/ui-gates** `9bd3d2c7` (`8a4a897c`): the TUI keeps `Final` and `Reorg`, `ask_final` and
  `check_reorg`; `included.rs`'s test takes lc9-ui-b's `proved::Final`.
- **lc9/ui-recheck** at UI_COMPOSED `934f687a` (`d8f7fb08`), posted before this merge, so no
  Lean-only merge follows: `snapshot::recheck` keeps lc9-ui-a's body (`lc_check::record_account`,
  which refuses a record with a name fact); `check_anchor`'s new leading chain argument passed by
  the live harness, the configured chain, never an answer's.
- **lc9/own-node** `e9331a64` (`6e3a9ef8`): clean.

Three fixes after the merges, one commit each naming the cause: names and prices take the pin
gate's configured rule (`461f6b6d`, D60: a name typed in a command `lkd` did not start, netd
running beacon sources and `lkd-lc` down, read as if no light client were configured, with no
`W`); a name proved at a block the reorg check finds replaced blocks its review until looked up
again (`d2a1130e`, D39: a review's own `Named` was not withdrawn, lc9-ens having built on the
reorg stub); the live run's request budget counts the slots and epochs any window spans
(`efaa42b3`: a refresh crossing an epoch on mainnet would have read as the wallet's failure).
The last two came from an independent review of the merged tracks and were checked here
against the code and their tests before they were applied.

**The verification, once** (`scratch-lc9/design/verification.md`; each check's own success line,
2026-10-27): `just extract` (git clean) and the `Funs` build; the four core static libraries;
`lake build` (3,852 jobs, no `sorry`); `check-axioms.sh` (5,012 theorems); `check-core.sh` (each
library, rule 5 on every row, 27 abort sites); `check-kernel.sh` (631 modules, 519 s, two jobs);
`proofs/tests` (BLS all ok, SSZ 444, store 224 with 3 unsupported, plan 482, inclusion 645,
pins 591); nightly `fmt`; workspace clippy and `lkd-lc`'s with `dev-insecure`; `cargo test`
(124 binaries, 1,151 passed, 4 ignored; `lkd-ui` 226 + 2); `lkd-lc-incl-test --budget`; Kani
`lkd-lc-core` (8 of 8) and `lkd-verified` (32 of 34: `snapshot::verification::parse_lengths_total`
and `decode_short_total` run out of CBMC's 16 GB since lc9-ens's name facts put two nested
vectors on `parse`'s paths, no counterexample; `parse`'s totality on every input is
`Refinement.Snapshot.parse_spec`'s; an unwinding bound to their reachable loops was tried and
still ran out, and was not kept: open); `release-check.sh`; the LC9 scenarios; the survey; the
live run; then the other 83 scenarios of the wallet suite (`e2e: all scenarios passed`, 43 min),
after every fix below. `just kani`'s `lkd-k256` harness stays broken since `3fd6afe`
(pre-existing, not run).

The LC9 scenarios' first run passed `lc-proof-window`, `lc-deadlines` (its 90 s precondition
measured at 27 s), `lc-live-dry` (the budget formula's fix: 34 `finality_update`s against 46),
`lc-final` and `lc-fail-closed`, and found four causes in the harness, each fixed in a commit
of its own and its scenario rerun alone: a fixture keystore's wallet copied the world's
spending ledger, which master's keyd seals with the world's keystore's key (`lc-name-facts`;
`98df8a0d`); the mover could mine one more block after a hold, and lkd-lc could still be
catching up with the last block served (`lc-names-anchored`'s stale anchor; `326fd611`); and a
chain held longer than a development sync period (64 s) left a period with no block, for which
the fake beacon wrote no update, so the light client, which never skips a period, stopped
following it (`lc-names-anchored` after its release, `lc-reorg`'s reorg check and its stale
review; netd's traffic showed lkd-lc asking `updates?start_period=4` and the fake beacon's 404;
`830d49fc` fills such a gap as `Chain::start` fills the chain). Then `lc-name-facts`,
`lc-names-anchored` and `lc-reorg` passed, `lc-reorg` with its D58 half for the first time: a
deposit's review proved at block 131 blocked as stale past 90 s, then passing at block 165 once
the anchor moved and its batch was asked again; its reorg check withdrew block 74 and proved
again at 123 with two `History` reads, none on an address's circuit. lkd-lc's catch-up itself
was never in question: a real chain has blocks in every period.

**The live run** (D52, over Tor, read-only, fresh wallets of anvil's words; stage 0 refused the
release build's `--check-mlock`, so every verdict is the debug build's with keyd's
`--no-mlock`: "debug build: this host refuses mlock"):

- **Mainnet, green on its second run** (22:03 to 22:10 UTC, after `710cb364`, which `lc-live-dry`
  passed alone): the proposal 2 of 2 sources agreeing, 3 configured (Lodestar did not answer the
  grid root); no development option in the six daemons but keyd's `--no-mlock`; anchored at
  block 26,286,908, 512 of 512 signing, final up to 26,286,843; `Account`, `AccountFinal`,
  `Head(0)`, `Head(1)`, `BlockHash(26,286,906, 0)` proved at the anchor and `BlockHash(F, 1)`,
  4 tokens, 20 pins (no table drift), 6 pools and `Included` at block 26,286,844 (proved at
  26,286,875), each against the oracle's reads at the same block hash; `lkd status` anchored;
  `vitalik.eth`, its primary name and the prices read at the anchor; the request budget over a
  42 s refresh, the light client's classes only: `finality_update` 3 of 11, other beacon `GET`s
  0 of 3, `ElHeader` 1 of 6, `HeaderAt` 1 of 6, `ElProof` 1 of 1 per address and anchor,
  `History` 0 of 4, other storage reads 0 (the UI's 13 other requests printed, not judged); the
  snapshot pass at F: one `ElHeader`, one `ElProof`, no token storage of 4. Its first run
  (21:41 UTC) had stopped at stage 4, "Pool(5): not a pool answer (no request failed)": the
  Privacy Pools association set's query answered something else than a pool, which the harness
  did not record (it names the answer since `710cb364`); the same query answered on the second
  run, and its proofs at the head (six slots, 15 KB) fit an answer, so the cause stays unknown.
- **Sepolia, inconclusive twice**, for the user's word: on the first run (21:41 UTC) the proposal
  had 2 of 2 sources agreeing and the overview showed the balance anchored, 512 of 512 signing,
  final up to block 12,007,819, under Gloas on ethPandaOps' Nimbus route and Lodestar; stage 6
  waited 720 s for the first snapshot pass while OnFinality answered the pools' `eth_getLogs`
  429, which the probes met again (49 of 75 failed requests not answered). On the second (22:54
  UTC, after a pause of 52 min) no checkpoint was proposed: netd's streams to both sources failed
  at tor's SOCKS socket, "Resource temporarily unavailable", and the probe met ethPandaOps'
  connection timing out after 8 s while Lodestar answered.

**Step 7, UI_COMPOSED** (after the live run, at `39a26978`): lc9-ui-a posted `934f687a` before
step 3, which merged it (`d8f7fb08`), so `git merge --no-ff` found nothing to merge and nothing
was committed. Its checks passed once more at the tip: `lake build LkdProofs.Lc.Ui` (1,735 jobs,
all up to date, no `sorry`), `check-axioms.sh` (the same 5,012 theorems; the 16 `Lkd.Lc.Ui`
lines on `propext`, `Classical.choice` and `Quot.sound`, `causeOf_matched` on `propext` alone)
and `check-kernel.sh` (631 modules, 447 s, two jobs); no e2e was run again. What lc9-ui-a left
unproved: `Ui.name_sound` and `Ui.prices_sound` (the re-checked `Head`'s root with `Spec.Ens` and
`Spec.Prices`) are not built, so a name or a price at the anchor rests on checks proved one by
one and not composed: its header (`Ui.head_sound`, `lc_check::fresh`), then
`ens::{forward, reverse, primary}` and `prices::{quote, sqrt_price}` under that header's root
(28h, 29g), the glue between them tested; and, for every composed pair, which re-check each
screen calls with what it asked, the words and the rendered lines (D49's value level) stay
tested.

**The review's fixes** (2026-10-28, after `2a1c6154`): four independent reviews of the merged
tree (egress and privacy, the Lean statements, the UI's gates and flows, the runtime's storage
and ABI) found sixteen defects, each confirmed against the code before it was fixed here, one
commit per cause:

- **Storage.** keyd's `History` lost and repeated records past one frame: `encode_records`
  skipped a record that did not fit and kept later ones, while `Keyd::history` asks the next
  page from the count received, routine on mainnet with D48's name records; a page now stops at
  the first record that does not fit (`0333d0ca`).
- **D43.** A fetch timed out unstarted stopped counting at its `Started`, though netd then serves
  it, so a fetch sent meanwhile waited behind two services; it counts until its page or failure
  (`0e6c227b`). The UI's netd timeout is a budget, not a bound: `UI_FRAME_MS` is one read's wait
  and a frame reading several times holds netd longer (`e9c19426`, 25r).
- **D39.** G9's check knew only answered reads, so a `History` read could go out at the anchor of
  an `Account` read still in flight (LC1's differential, a read `lkd-lc` still fetched) or, asked
  again, at a block it never checked: `Account` and `Token` reads now count from their first ask
  (`proved::AccountRead`, which the shared wait waits on too, so D37's pins and pools gain it), an
  unanswered read naming `lkd-lc`'s anchor as it ends, and the check asks only with none in
  flight or begun, an answer at an anchor it did not accept skipped (`0532eafc`); each round
  accepts a moved anchor again by the same rule, since with no read begun it is past every anchor
  a read of this UI was asked at (`ff19e6b8`: stopping at the first move, the check never got an
  answer in the suite's `lc-reorg`, a block coming every three slots on a loaded machine).
  The window's lead named the contracts for a review held by a replaced recipient name
  (`a9f06550`).
- **D58.** A stale review batch was asked again at each refresh even when no batch could be fresh
  (a clock ahead of the chain's, which `lkd-lc` never flags, or a stalled chain): only at a fresh
  anchor now, the words naming the anchor's age (`e0fe2abf`); a send's name proved at the anchor
  never aged in an open review: its provenance keeps the header's timestamp and counts at each
  evaluation (`722dd1c1`); the command line evaluated its gates once and then waited on standard
  input with no limit: `still_gated` counts them again at the last answer (`258f8bc4`).
- **D44, D45.** A name kept on the quorum path was read again every epoch, light client down or
  not: only while it anchors now, and 28h, 17-ens and D44 state what each re-read costs
  (`4c0b518b`); `lkd send <name>` read the sender's account at the same anchor right after the
  name's lookup: the account's read now waits one slot and the spread past it (`fe103447`).
- **The statements.** `Ui.pin_sound` keeps `namesPinned` (`73c6b2c7`); `Ui.blockHash_sound` takes
  `reorg::judge`'s checks as hypotheses and concludes `Configured` and `Replies` for the
  `BlockHash(n, isFinal)` asked (`eab7cddc`); key set 6's issuance at P's EL hash is reviewed and
  tested, no theorem stating it (`6076c07c`: 25x, 10i, Audit); 28h, 29g, 15j and 17-ens state
  D60's configured rule (`77a6ed47`); the record theorems cover the records `lkd-lc` makes, whose
  facts the snapshot pass merges into the records it writes, D47's name records beside them, not
  composed (`5a94a04d`: 25s, 25y).

The checks, each once unless said, at the fixes' tip: `just extract` (`crates/verified` changed;
git clean) and the `Funs` build; `lake build` (3,852 jobs, no `sorry`); `check-axioms.sh` (the
same 5,013 lines, `Ui.pin_sound` and `Ui.blockHash_sound` on `propext`, `Classical.choice` and
`Quot.sound`); `check-kernel.sh` (631 modules, 775 s, two jobs); no runtime Lean changed, so no
`check-core.sh`; nightly `fmt`; workspace clippy (four runs: functions over clippy's line limit,
which the fixes then shortened), `lkd-lc`'s with `dev-insecure`, and `lkd-ui`'s after `ff19e6b8`
(two runs, a test split); the tests of what changed (`lkd-verified`'s journal and deadlines,
`lkd-lc`'s `tests/shell.rs`, `lkd-keyd`'s journal and snapshot tests, `lkd-ui` 230 + 2, `lkd-gui`
39); the whole e2e suite once, 89 of its
91 scenarios passing, then its two failures alone: `lc-pools` (the harness's own `cast call` to
anvil refused under the machine's load) passed as it was, and `lc-reorg` (the check's stopping
rule above) passed after `ff19e6b8`: block 77 withdrawn and proved again at 148, two `History`
reads, at most two a check, none on an address's circuit nor at the `Account` reads' block hash
before it, then D58's stale review blocked past 90 s and passing at block 193 once its batch was
asked again at a fresh anchor; `release-check.sh`. Not run: `lean-gate` (the user's word), Kani
(no harness covers `encode_records` or the shell's `Flights`), and the live run, though the fixes
change what it drives (the reorg check's `History` reads and the shared reads' waits, names in an
open review and on the command line): it is the user's to run again.

## Storage batches (2026-10-29)

**Why.** In the user's Sepolia session of 2026-10-29, the light client's storage reads at one
anchor (pins, tokens, pools: 19 of them) went out one after another, each `ElStorage` a request
of its own, 2.2 s each at ethPandaOps (its time to build a proof by block hash; 0.14 s at
0xRPC): 40 s before the review's pins or the tokens could show. Measured directly the same day,
19 `eth_getProof` calls in one JSON-RPC batch took 2.16 s at ethPandaOps and 0.23 s at 0xRPC;
OnFinality refused a batch (429). The user chose (2026-10-29) a batch fetch end to end.

**The fetch.** Channel kind `0x16`, `ElStorages(attempt, h, ks)`: attempt (1), block hash (32),
the count (1: 2 to `MAX_BATCH`, 24), then each key set as `ElStorage` writes it (`0x15`: its tag
and arguments, at most 41 bytes); a datagram of at most 1,031 bytes, a fetch of at most 1,019. A
count outside 2 to 24 is refused. netd answers G12's key set 7 (`HistoryFor`) in a batch
`Denied`: egress never batches it, and the planner never puts it in one. Its response,
paged as a block body's ([D12](#decisions)): the count (1), then per key set, in the request's
order, a status (1: `0` answered, else the channel's failure code for that key set alone) and,
when answered, the length (4) and `ElStorage`'s response (`StorageProof`, at most `MAX_PAGE`).

**netd** routes each key set exactly as it routes an `ElStorage` today: its endpoint
`el_endpoint(key, attempt)`, its isolation group `keys_group` (`Token(i, owner)` on
`Account(owner)`, the others on `Shared`). It groups the key sets by (endpoint, group), in the
request's order, and sends each group as one JSON-RPC batch (`egress::Request::StorageBatch`),
one group after the other, within the fetch's deadline (`EL_MS`). No key set reaches an endpoint,
or goes over a circuit, it would not reach or go over as an `ElStorage` at the same attempt; what
a batch adds is that an endpoint gets at once the requests it got back to back over one kept
stream. A group the endpoint refuses (an HTTP error, a reply that is not an array of as many
answers, by id) fails each of its key sets with the channel's code; the others stand.

**Egress (10i, restated).** `Request::StorageBatch { chain, keys, hash }`: 2 to 24 typed key sets
(`egress::Keys`), each deriving from the chain's pin table as `StorageByHash`'s must, all of one
isolation group, which is the request's; its body is the JSON array of the `StorageByHash`
bodies of its key sets, in order, with ids 0 to n − 1. Nothing else is batched.

**The planner** (`PlanStorage.cands`, `Plan`): the storage reads waiting at one EL hash with the
same attempt are asked together, up to `MAX_BATCH`, as one fetch and one job (a single read
stays an `ElStorage`). A batch's answer is delivered key set by key set through `deliver`, so
each response is checked as today (25j, 25k); a key set that failed, or every key set of a batch
that failed or timed out, goes to `fail` as an `ElStorage` would, and is asked again, one attempt
more, with the other reads at that attempt (netd then picks the next endpoint for each). So an
endpoint that refuses batches costs one attempt, not the read. A read is not asked while a fetch
in flight asks it, alone or in a batch (`Plan.storageInFlight`).

**As built (2026-10-29).** `egress::batch_bytes` (10i), channel kind `0x16` in the core
(`LkdLc.Wire`) and in Rust (`lc_channel`, refined), the planner's grouping (`Plan.storageCands`,
`groupStorage`, `storageBatch` = 24) and fan-out (`deliver`, `fail`), netd's
`lc_storage::el_storages` and `Node::storage_batch` (over IPC the reads of a batch go one by
one: netd matches IPC answers by id on one connection), `lkd-lc-core`'s effect lengths. netd's
recent-answer cache (`by_hash`) keeps no batch. In `net.tsv` a batch is one `call` row,
`eth_getProof xN @host`, and one `lc` row, `ElStorages`. D37's
wait and D2's batch are untouched: a batch holds only reads the planner would have sent at that
moment.

## Milestones

Each milestone ships code first, then its proofs right after.

| | Ships | Accepted when | Size |
|---|---|---|---|
| **LC0** Tooling and Lean 4.35 | `build/turbo-lean`, which carries the 4.35 bump; on top of it, as committed on `build/lc0`: `check-kernel.sh` and the `debug.` ban in `just proofs`, `lean-gate`'s text checks over tracked sources, `CheckCore` and `check-core.sh` over a list of runtime libraries with theorems' axioms included, and the guarded-signing renumbering; then `lean-gate`'s merge-base, the builtin-abort allowlist, the lean-native docs corrected, D7 (`Nat.powMod` with `powMod_def`; `Pratt.powMod`, `Ecdsa.powModAux`/`powMod` and `Mont.powModFuel` retired; one primality engine); D19 (`VCVio.Algorithms.Sha2` for the vendored SHA-2, `compress_eq` re-proved over `RoundState`) | The `False` probe fails `just proofs`; an unlisted `@[csimp]` fails `lean-gate`; `lean-gate` passes on a fresh clone after `just proofs` | M (D19's re-proof: cost unknown) |
| **LC1** `lkd-lc` with real code | `LkdBase`, and `keyd` linking it; `crates/lean-rt`, `crates/lc-core` and the sandbox (26a); the evidence copies; the channel (25q) and netd's loop; supervision; lcproto in `lkd-verified` (25o); `El` moved and cleaned (the `RlpDecode` split, the `ByteArray` reader, 14b restated); 19b restated; `lkd-lc` runs today's quorum account check in Lean (one endpoint's since 2026-10-28), differential against `check_proved` | Every e2e scenario green; `lc-killed`, `lc-killed-mid-page`, `lc-netd-restart`, the soak | M/L |
| **LC2** Every balance and nonce, on the quorum path (one endpoint's since 2026-10-28; built 2026-10-26 on `lc2/work`: [G10](#every-eth-balance-g10) and [G11](#stuck-settled-and-foreign-nonces-g11) as built; 25m proved; e2e `proved-balances`, `foreign-nonce`, `settled-nonce`) | G10's call sites through `ProvedAccounts`, G11's rules and call-site table in `lkd-verified`, the labels; 25m | e2e; 25m proved | S/M |
| **LC3** SHA-256 and SSZ (built 2026-10-26: ssz-specs vendored; roots, branches, gindices, framing proved; decoders tested) | ssz-specs' gate, then the dependency or the vendored copy; `LkdBase.Sha256`; the typed decoders proved equal; framing, BPO digests; 25a, 25b | `ssz_static` and `single_merkle_proof`; SHA-256 at 7 ms per MiB or less | M to L if ssz-specs builds as a dependency (decoder equalities over its dynamic universe, untried); L if it must be vendored and repaired |
| **LC4a** BLS at runtime | `Bls.*` in CoreVerify's arrangement, the identity and SSWU refusals, the constants pinned with kernel checks; EthLib vendored and made total. Built on `lc4a/work`: `LkdLc.Bls`, `LkdProofs/Vendor/EthLib/Bls`, `proofs/ABORTS.allow`, `proofs/tests` (`lkd-bls-test`) | Every BLS and RFC 9380 vector; at most 20 ms per update (15 ms if decision 12 keeps G.3). Met: 147 vector checks pass on both layers; an update 17.0 ms with `[h_eff]P` | M |
| **LC4b** BLS proofs | 25c: `Fp2` as `QuadraticAlgebra`, `Fp6` and `Fp12` fields, `G1Group` ported over `[Field F]`, decompression, `hash_to_G2`'s equalities, the cube lemma. Built on `lc4b/work` (`LkdProofs/Lc/Bls`): primes, `Fp` and `Fp2` against `ZMod p`, `QuadraticAlgebra` and EthLib, `Fp6` and `Fp12` fields (Kummer, not CompPoly), the a = 0 Jacobian for G1 and G2 with `[r]G = O`, decoded points on their curves and in the subgroup, the cube lemma, FastAggregateVerify as e(g₁, σ) = e(Σpkᵢ, H(m)) under H_vec's hypotheses, decoding unique. LC4b's rest (`lc4b/rest`): decoding canonical and complete, `hash_to_G2` equal to EthLib's step by step, `HashOnCurve` proved (the isogeny's identity checked by the kernel), EthLib's G1 and G2 formulas and `Fp2.sqrt` proved. FastAggregateVerify equal to EthLib's where H(m) is not the identity and the signature not the identity's encoding, that case characterized (e(Σpk, H(m)) = 1) | 25c listed in `Audit.lean`. Met in part: the row says what is proved | L at its upper end, uncertain: the `Fp6` and `Fp12` field proofs are untried. They went through; the kernel, reducing a runtime function's matches in place, evaluates `Nat.powMod` on symbolic arguments and runs out of stack, so proofs rewrite the matches to `Option.elim` first |
| **LC5** The store (built 2026-10-26 on `lc5/work`: [as built](#the-store-and-the-evidence-as-built-lc5); every `sync` and `update_ranking` vector passes under its rules, the forced steps unsupported) | `Store`, `Forks` (Sepolia's Gloas), the clock, `MAX_AGE`, conflicts and the retained checkpoints, `Load` and `Persist`; 25d to 25i, 25n | `sync` and `update_ranking` vectors, under their rules | L |
| **LC6** Anchored reads (the core built 2026-10-26 on `lc6/core`: [the planner and anchored reads, as built](#the-planner-and-anchored-reads-as-built-lc6); 25j, 25k, 25p for balance and nonce proved; `NotAnchored`; `lkd-e2e-beacon-gen`; `lkd-lc-plan-test`; the UI's track built 2026-10-26 on `lc6/ui`: the configuration keys with 25e's round trip, `lkd init`'s fourth question, the `--propose`/`--check` flows in `lkd` and `lkd settings`, G10 and G11 asking `lkd-lc` first with the re-check, the head cross-check and the labelled fallback, Settings' group, the fake beacon server, `lc-anchored-cli` and `lc-settings-cli`; integrated 2026-10-26 on `lc6/integrate`: `lkd-lc --propose`/`--check`, the fake beacon on the generator's chain over anvil, the 13 other `lc-*` scenarios run; the refresh's move not built) | Egress 10i, netd's beacon client with JSON re-encoding, the planner, EL anchoring, the head cross-check, G10 and G11 anchored, `--propose` and `--check` with the refresh, Settings, the fake beacon, the survey; G19's snapshots (the `Snapshot` journal record, `CheckSnapshot`); 25j, 25k, 25p for balance and nonce, 25s for snapshots; 19a restated | The `lc-*` scenarios; G1 to G11 shown; the per-refresh request budget held in `e2e-lc-live` | L |
| **LC7** Pins, tokens, pools (built 2026-10-27 in parallel tracks, integrated on `build/lc78-integrate`: [LC7 and LC8](#lc7-and-lc8-the-design-as-decided), [as built](#as-built); the user's answers D1, D2, D6, D22 and D34 built; 25t proved, 25k and 25s restated, 25v's formats proved, its store and checks and 25w tested) | The key survey, `Pins` with storage conditions and implementation proofs (D16: one Lean table, the Rust refined against it), G14 to G16 with D1's gates; G19's public caches (pool trees, Tornado spent sets, Privacy Pools' deposits, withdrawals and ragequits, ASP leaves, stealth announcements; one file per chain, 26a restated) and token facts in snapshots (D22); the head cross-check by header (D35); 25k for storage, 25t, 25v, 25w | Differential against `eth_call` at recorded blocks (`lkd-lc-pins-test`, `lkd-lc-plan-test`); e2e `lc-tokens`, `lc-pins`, `lc-pools`, `lc-tokens-ui`, `lc-pools-ui`, `lc-cache` | M |
| **LC8** Inclusion (the core built 2026-10-26 on `lc8/core`: [as built](#inclusion-as-built-lc8-core); 25l proved; at most 0.50 s per transaction on mainnet's and Sepolia's largest measured blocks. Phase 2 built 2026-10-27 with LC7: [as built](#inclusion-as-built-lc8-phase-2); D36's order, G12's job in `lkd-lc`, netd's bodies and held pages, journal kind 9, the UI's states with D3's and D7's rules, `lkd status`'s exit 7; the user's answers D3, D4 and D7 built; 25u proved) | The trie builder against the Yellow Paper's trie (`Spec.Mpt.Trie`), EIP-2935, paging, the `Included` record and its outcomes, the journal codec restated; 25l, 25u | `lc-mined`, `lc-mined-ui`; at most 1 s per transaction on mainnet's and Sepolia's largest measured blocks, and the whole job within 1 s on the two kept blocks (`lkd-lc-incl-test --budget`) | L |
| **LC9** Live (built 2026-10-27 in seven tracks, integrated on `build/lc9-integrate`: [LC9: the design as decided](#lc9-the-design-as-decided), [as built](#as-built-lc9); the user's answers D39 to D60 built; 25x and 25y proved, the UI's halves composed with `lkd-lc`'s (but names and prices); the integration and its live run: [as built](#the-integration)) | `AccountFinal` (G11's "settled at block F, final", D7's outcome 1) and G9's reorg check by `History(N)` on `Shared` (D25, D38 to D40); `Head` and `BlockHash`; "your node refuses proofs at block N" ([The node's proof window](#the-nodes-proof-window), D42); D43's deadlines; the UI's halves of the composed theorems (D49 to D51: `lc_check`, `pin_gate`, `inclusion_keep`); freshness where a value gates or pays (D58); D1 failing closed without `lkd`'s settings (D60); ENS names and prices at the anchor and the selected account's primary name as facts (D44 to D48, in place of the deferred `lc9/quorum-pins` and `lc9/ens-facts`); public beacon sources an opt-in on your own node's route (D53); `e2e-lc-live` and `--lc-survey` (D52); `INVARIANTS.md` and `AGENTS.md` final | Live runs green (a debug-build green recorded as such, D52). **2026-10-27, debug build: this host refuses mlock**: mainnet green on its second run (anchored at block 26,286,908, 512 of 512 signing, final up to 26,286,843; every answer as the oracle's, 20 pins with no table drift, 6 pools, `Included`; names and prices at the anchor; the budget within its classes), its first run stopped at stage 4 on an unrecorded answer to `Pool(5)`; Sepolia inconclusive twice (OnFinality's 429s on `eth_getLogs` keeping the first snapshot pass back, then no checkpoint proposed through tor's SOCKS socket), anchored once at 512 of 512 under Gloas: for the user's word ([the integration](#the-integration)) | M |

**Build and CI** (LC1): `crates/lc`, `crates/lc-core` and `crates/lean-rt` are workspace
members, not default members, as `core` and `keyd` are (`crates/Cargo.toml:2-24`). `just lc`
builds `LkdLc:static` and runs clippy and the tests of `lkd-lc-core` and `lkd-lc`; `ci` gains it.
`e2e` and its variants, `release-check.sh` and `dist.sh` build `LkdLc:static` (and, for e2e,
`LkdLcDev` and the fake beacon) and `-p lkd-lc`; `release-check.sh` adds `lkd-lc` to its binaries
and its `dev-insecure` refusal; `dist.sh` and `install.sh` ship it, built reproducibly.

**Dependencies.** LC1 needs LC0. LC2 needs nothing: it uses today's `ProvedAccount` path, and
LC6 points it at `lkd-lc`. LC3 needs LC1's base library. LC4a needs only LC0, and runs in
parallel with LC1 to LC3; LC4b follows it. LC5 needs LC3 and LC4a. LC6 needs LC1, LC2 and LC5.
LC7 needs LC6, though its key survey can start at any time. LC8 needs LC6; its trie builder can
start after LC1, whose `ByteArray` RLP it reuses. LC9 needs the rest, LC4b included.

About 8 to 9 months for one engineer, or 6 to 7 with a second engineer on LC4b (*estimate*).
LC2 gives users proved balances everywhere at about 6 weeks; LC6 anchors them at about 6 months.

## Risks

- **EIP-8390, "Remove the Sync Committee"** (Draft, 2026-08-22): "It breaks every deployed
  Altair light client", replacing the committee with off-chain ZK proofs of FFG finality, with
  no proof format and no fork named yet. *Mitigation*: the anchor is an interface (a verified
  EL hash and its label). `El`, `Facts`, `Pins`, G10 to G16, the evidence plumbing and the UI do
  not depend on the committee; only `Store` and `Bls` would be replaced. Track All Core Devs.
- **Proof cost**: ssz-specs' build on 4.35, the `Fp6` and `Fp12` field proofs and D19's
  `compress_eq` are untried (LC0, LC3, LC4b). Mitigations: N7, the cube fallback, equalities
  proved in `LkdProofs`.
- **One verifier decides consensus** (open decision 20): mitigations are the vectors, fuzzing,
  the differential tests, the UI's re-check and the head cross-check.
- **Few sources**: on Sepolia two suggested light-client sources (ethPandaOps' Nimbus route and
  ChainSafe's Lodestar, which serves no bootstrap at a grid root since Gloas), on mainnet three
  (open decision 2); few serve grid bootstraps, which `lkd-lc` therefore fetches while they are
  current, and whether each answers over Tor is what the survey reads ([The
  survey](#the-survey-2026-10-26)).
- **reth** proves at the tip only by default ([The node's proof window](#the-nodes-proof-window)).
- **Specification churn**: each fork can move types (Gloas did; EIP-7688 keeps gindices stable
  from there). An unknown fork fails closed, so a release must precede each fork's epoch, or
  the wallet falls back, loudly, to one endpoint's head (a quorum's until 2026-10-28).

## Pinned sources

| Source | Pin |
|---|---|
| consensus-specs | v1.7.0-beta.4 (`aa16bb4`, 2026-10-08, pre-release; CC0-1.0) for the vectors and the specification; master `b834fa8` (2026-10-23) read for Gloas, whose light-client text is identical, and EIP-8198; v1.6.1 (`5fa6edc`), the latest stable |
| beacon-APIs | `79b9b05` (2026-10-20) |
| eth-clients | mainnet `8cad480`, sepolia `7b1b9d9`, hoodi `2a7efb3` |
| EIPs | `e858e91` (2026-10-24) |
| execution-specs | `e1a316a0` (`tests-zkevm@v21.0.0`, the pin leanerSTFSpec's `reference.toml` names), read for the trie, the transaction and receipt types and their insertion (`merkle_patricia_trie.py`, `forks/amsterdam/{fork,transactions,blocks}.py`) |
| helios | 0.12.0, `2af9b41887e069144ee56cd710f3ddca195473f8` (2026-10-05) |
| Lean | v4.35.0 (`eb6cafb`), Aeneas `74aabd5` (`build/lean-4.35`, `d2c94fa`) |
| ethereum/EthLib | `57af539e` (its Lean files are cryptography-specs `40db10a`'s) |
| ethereum/ssz-specs | `3394318c` |
| VCVio | `88efe971`, the dependency; `cbd4144b` and `afa6593f` only as the provenance of the vendored Keccak-256 (`LkdBase.Keccak`, first `LkdCore.Keccak`) and, until D19, `Vendor/VCVio/Sha2.lean` |
| Mathlib | v4.35.0 (`56a00585`) |
| CompPoly | `1cb8f5c` |
| leanerSTFSpec | `87754c75` |
| Lean oracles and alternatives | jaune `3e078b3a`, evm-asm `7e65e4d`, etheorem `54a3683`, CompElliptic `2c044403`, lean4-hash `ab7eda43` |
| Clients read | Lighthouse `a376def` (v8.3.2), Nimbus `0abc0dd` (v26.10.2), Lodestar `950d6b9`, Teku `2dc799f`, Prysm `8815a65`, Grandine `a638762`, go-ethereum `2006f08`, reth `f90ed27` |
| Oracles | py_ecc 8.0.0, blst v0.3.17 |
| RFC 9380 | Its J.10.1 vectors for `BLS12381G2_XMD:SHA-256_SSWU_RO_`, §8.8.2's `h_eff` and E.3's constants, read from the rfc-editor.org text (SHA-256 `a2e6ab02b2117d6f52ac293020857752972b2e23ae005c33f612e40436ff4b6d`) |
| ethereum/bls12-381-tests | v0.1.2 (`89ff3a86`, CC0-1.0), its `bls_tests_json.tar.gz` (SHA-256 `0dc1dfabfa7b3e0f8e8029f9cb2bb8733597526fa085b18f160d2c4eb0b448bc`); consensus-specs' `general.tar.gz` of v1.7.0-beta.4, SHA-256 `c4f395f71f606c28093500e32067990e430cc73a2277be6f3bf5090adcce3f67` |
| Development tools | turbo-lean `d4c5da92`, lean-native `8de44e78` |

## To confirm

1. ~~USDC's blacklist flag in bit 255 of its balance value, and the mask.~~ Bit 255, answered
   by LC7's survey: a balance is the word masked with 2²⁵⁵ − 1, and shown frozen when the bit is
   set (D17); `lkd-lc-pins-test` finds it set on the blacklisted holder only.
2. ~~The token keys on Sepolia; USDT's packed (`upgradedAddress`, `deprecated`) slot; Tornado's
   `currentRootIndex` and `roots` keys; Privacy Pools' `currentRoot`, `latestRoot` and
   `assetConfig` keys (LC7's survey).~~ Answered by the survey behind the tables of
   [Pins, tokens and pools](#pins-tokens-and-pools): Sepolia's USDC, WETH and LINK balances at
   positions 9, 3 and 0; USDT's slot 10, which must read 0 (D18: strict, gating sends); Tornado's
   slot 3, `currentRootIndex` in its low 32 bits, the root at slot 4 + i on mainnet's pools and in
   the mapping at slot 2 on Sepolia's; Privacy Pools' depth and size (slots 5 and 4) with the
   root in the mapping at slot 6, and the Entrypoint's association-set count (slot 2) with
   `assetConfig(ETH)` at `mappingSlot ethAsset 1`. Every key and value was checked at one block
   per chain whose hash two providers gave (`lkd-lc-pins-test`, [as built](#lc7-facts)); the
   table needed no fix.
3. ~~EIP-2935's history contract address at the pinned EIPs commit, and that its layout holds
   after Amsterdam.~~ `0x0000F90827F1C53a10cb7A02335B175320002935`, `HISTORY_SERVE_WINDOW = 8191`,
   slot `N mod 8191` (EIP-2935, Final, at `e858e91`); Amsterdam keeps it (EIP-7928, EIP-8037 do
   not change the layout). Checked on mainnet: proofs at the head prove blocks 7,650 back (LC8).
4. ~~Whether anvil produces Amsterdam (23-field) headers, and runs EIP-2935's system call with its
   history contract (else `anvil_setCode` and `anvil_setStorageAt`).~~ Neither, in Foundry 1.5.1:
   `--hardfork amsterdam` panics, and no system call runs even with the code set; so
   `anvil_setCode` and `anvil_setStorageAt` ([as built](#inclusion-as-built-lc8-core)).
5. Hoodi's genesis from `genesis.ssz`, still a Git LFS pointer (a fixture only).
6. ~~The survey: which public sources serve SSZ, grid bootstraps and Gloas data over Tor, the
   highest attested slot in `finality_update`, and `blocks/{slot}/root`; which D8 EL endpoints
   prove by block hash.~~ Answered over Tor at LC9's integration ([The survey](#the-survey-2026-10-26)):
   mainnet's Lodestar and the Nimbus team's node serve the four paths in SSZ, PublicNode in JSON
   only; on Sepolia ethPandaOps' Nimbus route serves them in SSZ with Gloas data and Lodestar all
   but the grid root's bootstrap; every suggested EL endpoint proves by block hash (OnFinality
   rate-limits).
7. That Nimbus's, Prysm's and Teku's Gloas light-client data match v1.7.0-beta.4 on the wire.
   Answered for Nimbus and Lodestar: LC9's live run anchored Sepolia, under Gloas, on
   ethPandaOps' Nimbus route and Lodestar, 512 of 512 signing. Still open for Prysm and Teku,
   which no suggested source runs.
8. That Mathlib's daily `leanchecker --fresh`, which runs on its master and nightly, covered the
   v4.35.0 commit we pin; else Mathlib and Batteries are replayed here once per bump.
9. ~~Whether ssz-specs builds unmodified on 4.35, and its SHA-256's speed.~~ It does not, as a
   dependency (its `warningAsError` and 4.35's deprecations), and is vendored; its SHA-256 hashes
   1 MiB in 5.59 ms (LC3, [Sources](#sources), [Speed](#speed)).
10. ~~G12's CPU and memory, and Sepolia's largest block and receipts.~~ 0.13 to 0.23 s a
    transaction on average, 0.50 s at worst, under 21 MB resident; Sepolia's largest of a week,
    block 11,985,890, 969,024 bytes, 2.07 MB of JSON ([Sizes](#inclusion-and-receipts-g12), LC8).
    (`[r]Q`'s cost: measured in LC4a, 2.41 ms with the signature's decompression.)
11. ~~RFC 9380 Appendix G.3 as `clear_cofactor`'s source, which the bench (`HashToG2.lean:106`)
    and EthLib (`HashToCurve.lean:201,244`) cite, against the RFC's text.~~ Moot since LC4a:
    `clear_cofactor` is `[h_eff]P`, §7's own definition, in both layers, `h_eff` taken from §8.8.2's
    text and checked against `3(x² − 1)·h₂` by the kernel (`Lkd.Lc.Bls.hEff_def`); EthLib's G.3
    code, kept as `clearCofactorG3`, gives the same points in the tests.
12. That libuv runs under `lkd-lc`'s filter (the soak test).
13. Whether tor's consensus time could bound the clock, and whether tor finishes a rendezvous
    after its stream is abandoned.
