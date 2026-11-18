# Recorded `eth_call`s

Public chain data, recorded from public mainnet and Sepolia endpoints in November 2026 (each
file's `#` lines name the blocks and the endpoints), and synthetic cases over public addresses.
`leanlight-evm-test` checks each file against `SHA256SUMS` before reading it.

Two formats, gzipped text, one item a line, hex with `0x`:

**`leanlight-evm-vectors 1`** (`*-corpus`, `*-edge`, `*-calls24`, `sepolia-second`,
`mainnet-proof-26435868`, `holes-eip7610`): the state each case read, as the node reported it,
then the cases.

| Line | Meaning |
|---|---|
| `code I 0xCODE` | code number `I`, held under its Keccak-256 |
| `case NAME` ... `end` | one case |
| `kind K`, `chain ID` | a label, the chain id |
| `header NUMBER TIMESTAMP GASLIMIT COINBASE MIXHASH EXCESSBLOBGAS BEACONROOT SLOT PARENTHASH` | the fields of the block the call ran at |
| `ancestors H...` | the block hashes before it, oldest first |
| `tx FROM TO|- VALUE GAS|- DATA` | the request (`-`: a creation, or no gas named) |
| `account A absent` | an account the node reported absent |
| `account A NONCE BALANCE cI|hHASH|- ROOT|-` | an account: its code (held code `I`, a hash only, or none) and storage root (`-`: not recorded) |
| `slot A KEY VALUE` | a storage word |
| `override A 0xCODE` | a code override the request declares (an input, not a fact) |
| `expect ran OK OUTPUT|- ERROR|-`, `expect refused CLASS`, `expect hole full|partial A` | the node's answer, its refusal, or an EIP-7610 case |
| `gas N`, `estimate N NODE|-` | EthLib's gas used; EthLib's least passing gas and the node's estimate |
| `log A TOPICS|- DATA`, `logs unrecorded` | the logs |
| `second OK OUTPUT|-` | a second node's answer, when it differed from the first's |

**`leanlight-evm-proofs 1`** (`*-proofs-*`): one block's `chain`, `block` hash and `headerrlp`,
the node's `eth_getProof` answers (`account A NODES`, `slot A KEY NODES`, the nodes of each proof
joined) and `code` lines, then cases as above (no state lines: the test reads the state from the
proofs with leanLight's readers).
