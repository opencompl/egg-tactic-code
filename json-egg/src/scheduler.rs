use std::fmt::{self, Debug, Formatter};
use log::*;
use egg::*;
use indexmap::IndexMap;

// Based or egg's `BackoffScheduler`
pub struct BoundedGraphScheduler {
    max_graph_size: usize,
    default_application_limit : usize,
    search_threshold : usize,
    stats: IndexMap<Symbol, RuleStats>,
}

#[derive(Debug, PartialEq)]
enum RuleStatus {
    Available,
    Paused,
    Stopped
}

use RuleStatus::{Available,Paused,Stopped};

#[derive(Debug)]
struct RuleStats {
    times_applied: usize,
    match_limit : usize,
    times_paused : usize,
    status: RuleStatus,
}

impl BoundedGraphScheduler {
    /// Set the initial application limit after which a rule will be banned.
    /// Default: 1,000
    pub fn with_initial_match_limit(mut self, limit: usize) -> Self {
        self.default_application_limit = limit;
        self
    }

    /// Set the initial ban length.
    /// Default: 5 iterations
    pub fn with_max_graph_size(mut self, graph_size: usize) -> Self {
        self.max_graph_size = graph_size;
        self
    }

    fn rule_stats(&mut self, name: Symbol) -> &mut RuleStats {
        if self.stats.contains_key(&name) {
            &mut self.stats[&name]
        } else {
            self.stats.entry(name).or_insert(RuleStats {
                times_applied: 0,
                times_paused: 0,
                match_limit: self.default_application_limit,
                status : Available
            })
        }
    }

    /// Never ban a particular rule.
    pub fn do_not_ban(mut self, name: impl Into<Symbol>) -> Self {
        self.rule_stats(name.into()).match_limit = usize::MAX;
        self
    }

    /// Set the initial match limit for a rule.
    pub fn rule_match_limit(mut self, name: impl Into<Symbol>, limit: usize) -> Self {
        self.rule_stats(name.into()).match_limit = limit;
        self
    }

}

impl Default for BoundedGraphScheduler {
    fn default() -> Self {
        Self {
            stats: Default::default(),
            max_graph_size: 2_000,
            // TODO: add a function that computes this from the rewrites! 
            search_threshold: 20,
            default_application_limit : 64,
        }
    }
}

impl<L> RewriteScheduler<L, ()> for BoundedGraphScheduler
where
    L: Language,
{
    fn can_stop(&mut self, iteration: usize) -> bool {

        let n_stats = self.stats.len();

        let mut paused: Vec<_> = self
            .stats
            .iter_mut()
            .filter(|(_, s)| s.status == Paused)
            .collect();

        if paused.is_empty(){
            true
        } else {
            let mut unpaused = vec![];
            for (name, s) in &mut paused {
                s.status = Available;
                unpaused.push(name.as_str());
            }

            assert!(!unpaused.is_empty());
            info!(
                "unpaused {}",
                unpaused.join(", "),
            );

            false
        }
    }

    fn search_rewrite<'a>(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, ()>,
        rewrite: &'a Rewrite<L, ()>,
    ) -> Vec<SearchMatches<'a, L>> {
        let stats = self.rule_stats(rewrite.name);

        if stats.status == Paused {
            debug!(
                "Skipping {} ({}-{}), paused.",
                rewrite.name, stats.times_applied, stats.times_paused
            );
            return vec![];
        }

        let threshold = stats.match_limit << stats.times_paused;
        let matches = rewrite.search_with_limit(egraph, threshold + 1);
        let total_len: usize = matches.iter().map(|m| m.substs.len()).sum();
        if total_len > threshold {
            stats.status = Paused;
            info!(
                "Banning {} ({}) : {} < {}",
                rewrite.name,
                stats.times_applied,
                threshold,
                total_len,
            );
            vec![]
        } else {
            stats.times_applied += 1;
            matches
        }
    }
    fn apply_rewrite(
        &mut self,
        iteration: usize,
        egraph: &mut EGraph<L, ()>,
        rewrite: &Rewrite<L, ()>,
        matches: Vec<SearchMatches<L>>,
    ) -> usize {
        //println!("egraph size: {}", egraph.total_size());
        if egraph.total_size() + self.search_threshold < self.max_graph_size{
        rewrite.apply(egraph, &matches).len()
        }
        else{
            // This is obviously super inefficient...
            // we should be able to try and reverse if we don't like it.
            let mut egraph_copy = egraph.clone();
            rewrite.apply(&mut egraph_copy, &matches).len();
            if egraph_copy.total_size() > self.max_graph_size{
                let stats = self.rule_stats(rewrite.name);
                stats.status = Stopped;
                0
            }
            else{
                //just reapplying; could otherwise use the copy here
                //but then I'd have to think about the references...
                rewrite.apply(egraph, &matches).len()
            }
        }
    }
}
