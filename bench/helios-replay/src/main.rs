//! Helios's consensus checks on leanLight's recorded runs (tests/fixtures), offline, timed: the
//! same bytes leanlight-bench replays. Median of N runs per step, in ms.
use std::{fs, path::Path, time::{Duration, Instant, UNIX_EPOCH}};

use alloy_primitives::B256;
use helios_consensus_core::{
    apply_bootstrap, apply_finality_update, apply_optimistic_update, apply_update,
    consensus_spec::MainnetConsensusSpec as S,
    types::{Bootstrap, BootstrapElectra, FinalityUpdate, FinalityUpdateElectra, LightClientStore,
        OptimisticUpdate, OptimisticUpdateBase, Update, UpdateElectra},
    verify_bootstrap, verify_finality_update, verify_optimistic_update, verify_update,
};
use ssz::Decode;

fn meta(dir: &Path, key: &str) -> String {
    fs::read_to_string(dir.join("meta.txt")).unwrap().lines()
        .find_map(|l| l.strip_prefix(&format!("{key} ")).map(str::to_owned)).unwrap()
}

fn median(mut v: Vec<Duration>) -> f64 {
    v.sort();
    v[v.len() / 2].as_secs_f64() * 1000.0
}

fn time<F: FnMut()>(n: usize, mut f: F) -> f64 {
    let mut v = Vec::new();
    for _ in 0..n {
        let t = Instant::now();
        f();
        v.push(t.elapsed());
    }
    median(v)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(15);
    let cfg = helios_ethereum::config::networks::mainnet();
    let forks = cfg.forks.clone();
    let genesis_root = cfg.chain.genesis_root;
    let genesis_time = cfg.chain.genesis_time;
    for dir in &args[2..] {
        let dir = Path::new(dir);
        let now_ms: u64 = meta(dir, "now_ms").parse().unwrap();
        let slot = (UNIX_EPOCH + Duration::from_millis(now_ms))
            .duration_since(UNIX_EPOCH).unwrap().as_secs().saturating_sub(genesis_time) / 12 + 10;
        let root: B256 = meta(dir, "checkpoint").parse().unwrap();
        let bs = fs::read(dir.join("bootstrap.ssz")).unwrap();
        let bootstrap = Bootstrap::<S>::Electra(BootstrapElectra::from_ssz_bytes(&bs).unwrap());
        // /updates chunks: u64le length (4 + ssz), 4-byte digest, ssz
        let raw = fs::read(dir.join("updates.ssz")).unwrap();
        let mut updates = Vec::new();
        let mut at = 0;
        while at < raw.len() {
            let len = u64::from_le_bytes(raw[at..at + 8].try_into().unwrap()) as usize;
            let ssz = &raw[at + 12..at + 8 + len];
            updates.push(Update::<S>::Electra(UpdateElectra::from_ssz_bytes(ssz).unwrap()));
            at += 8 + len;
        }
        let fin = FinalityUpdate::<S>::Electra(
            FinalityUpdateElectra::from_ssz_bytes(&fs::read(dir.join("finality.ssz")).unwrap()).unwrap());
        let opt = OptimisticUpdate::<S>::Base(
            OptimisticUpdateBase::from_ssz_bytes(&fs::read(dir.join("optimistic.ssz")).unwrap()).unwrap());

        let t_boot = time(n, || {
            verify_bootstrap(&bootstrap, root, &forks).unwrap();
            let mut s = LightClientStore::<S>::default();
            apply_bootstrap(&mut s, &bootstrap);
        });
        let mut store = LightClientStore::<S>::default();
        verify_bootstrap(&bootstrap, root, &forks).unwrap();
        apply_bootstrap(&mut store, &bootstrap);
        let mut t_upd = Vec::new();
        let mut refused = Vec::new();
        for u in &updates {
            let before = store.clone();
            t_upd.push(time(n, || {
                let mut s = before.clone();
                if verify_update(u, slot, &s, genesis_root, &forks).is_ok() {
                    apply_update(&mut s, u);
                }
            }));
            match verify_update(u, slot, &store, genesis_root, &forks) {
                Ok(()) => { apply_update(&mut store, u); }
                Err(e) => refused.push(e.to_string()),
            }
        }
        let before = store.clone();
        let t_fin = time(n, || {
            let mut s = before.clone();
            verify_finality_update(&fin, slot, &s, genesis_root, &forks).unwrap();
            apply_finality_update(&mut s, &fin);
        });
        apply_finality_update(&mut store, &fin);
        let before = store.clone();
        let t_opt = time(n, || {
            let mut s = before.clone();
            verify_optimistic_update(&opt, slot, &s, genesis_root, &forks).unwrap();
            apply_optimistic_update(&mut s, &opt);
        });
        let total = t_boot + t_upd.iter().sum::<f64>() + t_fin + t_opt;
        println!("{}: {} period update(s), median of {n} runs (ms)", dir.display(), updates.len());
        println!("  bootstrap      {t_boot:.1}");
        if !refused.is_empty() { println!("  refused        {refused:?}"); }
        println!("  period update  {}", t_upd.iter().map(|t| format!("{t:.1}")).collect::<Vec<_>>().join(", "));
        println!("  finality       {t_fin:.1}");
        println!("  optimistic     {t_opt:.1}");
        println!("  total          {total:.1}");
    }
}
