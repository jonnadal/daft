include "Seqs.dfy"

// This is a Dafny implementation of the example from James Wilcox's blog post "How to build
// a simple system in Verdi" (http://homes.cs.washington.edu/~jrw12/Counter.html). Rather than
// factoring out a reusable implementation of reliable network semantics with directed message
// delivery, this implementation simulates reliable broadcast. It also does not expose external
// inputs/outputs. These features were left out to keep this example minimal. Also note that we
// do assume in-order delivery here, again for simplicity.
module ReliableNetworkSemantics {
	import opened Seqs
	datatype NodeId = PrimaryId | BackupId
	datatype Msg = Inc

	method run()
		decreases *
	{
		var nodes := map[PrimaryId := 0, BackupId := 0];
		var network := []; // Multiset is more intuitive but has less language support.
		while (true)
			decreases *
			invariant PrimaryId in nodes && BackupId in nodes
			// Our safety property follows: any lag on the backup is accounted for by in-flight messages.
			invariant nodes[PrimaryId] == nodes[BackupId] + |filter(network, m => m == Inc)|
		{
			// Dafny needs help realizing that sending an Inc increases the number of messages matching
			// the Inc filter in our inductive invariant (safety property) above.
			filter_distributes_over_append(network, [Inc], m => m == Inc);
					
			var id :| id in nodes;
			match (id)
				case PrimaryId =>
					nodes := nodes[PrimaryId := nodes[PrimaryId] + 1];
					network := network + [Inc];
				case BackupId =>
					if (|network| >= 1) {
						var msg := network[0];
						if (msg.Inc?) {
							nodes := nodes[BackupId := nodes[BackupId] + 1];
							network := network[1..];
						}
					}
		}
	}
}

// Now let's look at a lossy network that can reorder messages. If we stick w/ the Inc approach,
// we'll have to supplement them with IDs and re-send until acked. Let's avoid the ID by just
// re-sending the updated count until acked.
module LossyNetworkSemantics {
	datatype NodeId = PrimaryId | BackupId
	datatype NodeState = PrimaryState(primaryCount: nat, isSyncing: bool) | BackupState(backupCount: int)
	datatype Msg = Propagate(propagatedCount: nat) | Ack(ackedCount: nat)

	// Now primaries and backups store different kinds of information. Unlike Coq, Dafny lacks
	// dependent types, so a map from node ID to state can't have a different state type based on
	// the ID, but we can associate each ID w/ a different state datatype constructor for a similar
	// effect.
	predicate is_node_type_safe(id: NodeId, state: NodeState) {
		match id
			case PrimaryId => state.PrimaryState?
			case BackupId => state.BackupState?
	}
	predicate are_nodes_type_safe(nodes: map<NodeId, NodeState>) {
		forall id: NodeId :: id == PrimaryId || id == BackupId ==> id in nodes && is_node_type_safe(id, nodes[id])
	}
		
	method run()
		decreases *
	{
		var nodes := map[PrimaryId := PrimaryState(0, true), BackupId := BackupState(0)];
		var network: set<Msg> := {};
		while (true)
			decreases *
			invariant are_nodes_type_safe(nodes)

			// We never propagate a count greater than the primary's
			invariant forall m :: m in network && m.Propagate? ==> m.propagatedCount <= nodes[PrimaryId].primaryCount
      // ... so the backup's count must never exceed the primary's
			invariant nodes[BackupId].backupCount <= nodes[PrimaryId].primaryCount
			// ... and in turn the acked count must never exceed the primary's.
			invariant forall m :: m in network && m.Ack? ==> m.ackedCount <= nodes[PrimaryId].primaryCount
			// Also note that we only stop syncing when the backup count reaches the primary count.
			invariant old(nodes[PrimaryId].isSyncing) && !nodes[PrimaryId].isSyncing ==>
			(nodes[BackupId].backupCount == nodes[PrimaryId].primaryCount)
			// Here's a more interesting property that Dafny can't prove by itself, and I don't have
			// the required lemmas worked out yet.
			//invariant nodes[PrimaryId].isSyncing == false ==> nodes[BackupId].backupCount == nodes[PrimaryId].primaryCount
		{
			// Lossy network semantics (re-ordering comes from the data structure).
			if (*) {
				if (|network| > 0) {
					var msg :| msg in network;
					network := network - {msg};
				}
			}

			var id :| id in nodes;
			var state := nodes[id];
			match id
				case PrimaryId => // Primary can increment, sync, or process an ack (and stop syncing).
					if (*) {
						nodes := nodes[PrimaryId := PrimaryState(state.primaryCount + 1, true)];
						network := network + {Propagate(state.primaryCount + 1)}; // Optional, and Dafny can prove this.
					} else if (*) {
						if (state.isSyncing) {
							network := network + {Propagate(state.primaryCount)};
						}
					} else if (|network| >= 1) {
						var msg :| msg in network;
						if (msg.Ack?) {
							if (msg.ackedCount == state.primaryCount) {
								nodes := nodes[PrimaryId := state.(isSyncing := false)];
							}
						}
					}
				case BackupId => // Backup only needs to process propagation messages.
					if (|network| >= 1) {
						var msg :| msg in network;
						if (msg.Propagate?) {
							var max := if msg.propagatedCount >= state.backupCount then msg.propagatedCount else state.backupCount;
							nodes := nodes[BackupId := BackupState(max)];
							network := network + {Ack(max)};
						}
					}
		}
	}
}
