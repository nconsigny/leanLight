| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB | leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB | = helios at block N | = endpoint at N | leanlight errors | helios not at N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nimbus+publicnode | 0 | 6 periods | 1.01 | 0.26 | 26 | 1.19 (0.91 / 0.28) | 0.32 | 27 | 12/12 | 14/14 | 0 | 2 |
| nimbus+publicnode | 1 | 6 periods | 0.91 | 0.17 | 24 | 0.82 (0.63 / 0.19) | 0.24 | 72 | 13/13 | 14/14 | 0 | 1 |
| nimbus+publicnode | 2 | 6 periods | 1.32 | 0.18 | 24 | 0.94 (0.66 / 0.28) | 0.33 | 72 | 12/12 | 14/14 | 0 | 2 |

Read set of 14 reads, median over 3 rounds:

| leanlight (one batch + checks) ms | helios, one call each ms |
|---|---|
| 92 | 449 |
