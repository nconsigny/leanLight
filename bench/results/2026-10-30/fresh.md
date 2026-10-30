| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB | leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB | = helios at block N | = endpoint at N | leanlight errors | helios not at N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nimbus+publicnode | 0 | 0 periods | 1.02 | 0.18 | 25 | 0.81 (0.73 / 0.07) | 0.12 | 27 | 13/13 | 14/14 | 0 | 1 |
| nimbus+publicnode | 1 | 0 periods | 0.83 | 0.19 | 25 | 0.26 (0.20 / 0.06) | 0.10 | 68 | 11/11 | 14/14 | 0 | 3 |
| nimbus+publicnode | 2 | 0 periods | 0.82 | 0.19 | 25 | 0.84 (0.74 / 0.09) | 0.13 | 68 | 11/11 | 14/14 | 0 | 3 |
| nimbus+drpc | 0 | 0 periods | 1.00 | 0.27 | 25 | 0.63 (0.57 / 0.06) | 0.36 | 68 | 0/0 | 14/14 | 0 | 14 |
| nimbus+drpc | 1 | 0 periods | 1.43 | 0.17 | 22 | 3.76 (3.70 / 0.05) | 0.31 | 68 | 13/13 | 14/14 | 0 | 1 |
| nimbus+drpc | 2 | 0 periods | 0.93 | 0.18 | 26 | 0.25 (0.19 / 0.07) | 0.36 | 70 | 13/13 | 14/14 | 0 | 1 |

Read set of 14 reads, median over 6 rounds:

| leanlight (one batch + checks) ms | helios, one call each ms |
|---|---|
| 1813 | 1111 |
