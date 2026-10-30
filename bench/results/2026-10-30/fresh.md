| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB | leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB | = helios at block N | = endpoint at N | leanlight errors | helios not at N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nimbus+publicnode | 0 | 0 periods | 0.96 | 0.27 | 24 | 0.68 (0.60 / 0.07) | 0.12 | 27 | 0/0 | 14/14 | 0 | 14 |
| nimbus+publicnode | 1 | 0 periods | 0.93 | 0.29 | 25 | 0.27 (0.25 / 0.08) | 0.13 | 65 | 11/11 | 14/14 | 0 | 3 |
| nimbus+publicnode | 2 | 0 periods | 1.02 | 0.30 | 25 | 0.36 (0.27 / 0.08) | 0.12 | 65 | 11/11 | 14/14 | 0 | 3 |
| nimbus+drpc | 0 | 0 periods | 0.95 | 0.18 | 23 | 0.34 (0.30 / 0.13) | 0.23 | 78 | 13/13 | 14/14 | 0 | 1 |
| nimbus+drpc | 1 | 0 periods | 0.98 | 0.18 | 24 | 0.33 (0.30 / 0.13) | 0.24 | 78 | 13/13 | 14/14 | 0 | 1 |
| nimbus+drpc | 2 | 0 periods | 1.09 | 0.26 | 25 | 0.28 (0.26 / 0.08) | 0.22 | 78 | 13/13 | 14/14 | 0 | 1 |

Read set of 14 reads, median over 6 rounds:

| leanlight (one batch + checks) ms | helios, one call each ms |
|---|---|
| 690 | 1108 |
