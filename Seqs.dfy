module Seqs {
  function method filter<T>(xs: seq<T>, pred: T -> bool): seq<T>
		reads pred.reads
		requires forall t :: pred.requires(t)
		ensures forall x :: x in xs && pred(x) ==> x in filter(xs, pred)
		ensures forall x :: x in filter(xs, pred) ==> x in xs && pred(x)
	{
		if |xs| == 0 then []
		else if pred(xs[0]) then [xs[0]] + filter(xs[1..], pred)
		else filter(xs[1..], pred)
	}
	lemma ex_filter() {
		assert filter([1, 2, 3], x => true) == [1, 2, 3];
		assert filter([1, 2, 3], x => false) == [];
		assert filter([1, 2, 3], x => x % 2 == 0) == [2];
	}
	lemma append_identity_left<T>(xs: seq<T>)
		ensures [] + xs == xs
	{}
	lemma append_identity_right<T>(xs: seq<T>)
		ensures xs + [] == xs
	{}
	lemma append_associative<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
		ensures (xs + ys) + zs == xs + (ys + zs)
	{}
	lemma filter_distributes_over_append<T>(xs1: seq<T>, xs2: seq<T>, pred: T -> bool)
		requires forall t :: pred.requires(t)
		ensures filter(xs1 + xs2, pred) == filter(xs1, pred) + filter(xs2, pred)
	{
		if (xs1 == []) {
		} else if pred(xs1[0]) {
			calc == {
				filter(xs1 + xs2, pred); { assert xs1 == [xs1[0]] + xs1[1..]; }
				filter(([xs1[0]] + xs1[1..]) + xs2, pred); { append_associative([xs1[0]], xs1[1..], xs2); }
				filter([xs1[0]] + (xs1[1..] + xs2), pred);
				[xs1[0]] + filter(xs1[1..] + xs2, pred);
				[xs1[0]] + filter(xs1[1..], pred) + filter(xs2, pred);
				filter([xs1[0]], pred) + filter(xs1[1..], pred) + filter(xs2, pred);
				filter([xs1[0]] + xs1[1..], pred) + filter(xs2, pred);
				filter(xs1, pred) + filter(xs2, pred);
			}
		} else {
			calc == {
				filter(xs1 + xs2, pred); { assert xs1 == [xs1[0]] + xs1[1..]; }
				filter(([xs1[0]] + xs1[1..]) + xs2, pred); { append_associative([xs1[0]], xs1[1..], xs2); }
				filter([xs1[0]] + (xs1[1..] + xs2), pred);
				[] + filter(xs1[1..] + xs2, pred);
				filter(xs1[1..] + xs2, pred);
				filter(xs1, pred) + filter(xs2, pred);
			}
		}
	}

	function method fold<T1, T2>(xs: seq<T1>, base: T2, fn: (T1, T2) -> T2): T2
		reads fn.reads
		requires forall t1, t2 :: fn.requires(t1, t2)
	{
		if |xs| == 0 then base
		else fn(xs[0], fold(xs[1..], base, fn))
	}
	lemma ex_fold() {
		assert fold([2, 4, 6], 0, (x,y) => x+y) == 12;
		assert fold([2, 4, 6], 1, (x,y) => x*y) == 48;
		assert fold([2, 3, 4], [], (x,y) => (if x%2==0 then [x] else []) + y) == [2, 4];
		assert fold([2, 3, 4], [], (x,y) => (if x%2==1 then [x] else []) + y) == [3];
	}
}
