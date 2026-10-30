| endpoints | round | checkpoint age | helios sync s | helios CPU s | helios RSS MB | leanlight sync s (net / verify) | leanlight CPU s | leanlight RSS MB | = helios at block N | = endpoint at N | leanlight errors | helios not at N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nimbus+publicnode | 0 | 6 periods | 1.03 | 0.30 | 25 | 1.06 (0.83 / 0.37) | 0.41 | 27 | 9/9 | 14/14 | 0 | 5 |
| nimbus+publicnode | 1 | 6 periods | 0.99 | 0.22 | 25 | 1.40 (1.22 / 0.27) | 0.37 | 56 | 10/10 | 14/14 | 0 | 4 |
| nimbus+publicnode | 2 | 6 periods | 1.10 | 0.27 | 25 | 1.00 (0.79 / 0.30) | 0.38 | 56 | 12/12 | 14/14 | 0 | 2 |

Read set of 14 reads, median over 3 rounds:

| leanlight (one batch + checks) ms | helios, one call each ms |
|---|---|
| 6 | 512 |
