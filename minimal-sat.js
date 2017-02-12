// In this blog post, we write a minimal [SAT](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) solver.
// A SAT solver determines whether a boolean formula can be "satisfied" (made true) by an appropriate assignment of `true` and `false` to the variables constituting that formula.
//
// For example, the boolean formula
//
// (x1 &rArr; x2) &and; (x1 &or; &sim;x3)
//
// corresponds with the equation
//
// true &equiv; (x1 &rArr; x2) &and; (x1 &or; &sim;x3)
// 
// which could be satisfied with the assignments
//
// (x1 &equiv; false) &and; (x2 &equiv; true) &and; (x3 &equiv; false)
//
// Note that while the SAT problem concerns itself only with the existence of such an assignment, when such an assignment does exist, our solver will emit it.
// This provides a way to easily validate our code, as an assignment can be verified in polynomial time.

'use strict';

const fs = require('fs');
const tape = require('tape');
const util = require('util');

//
// ## Examples ##
//
// Let's start by writing a test to outline what "correct" looks like.
// We introduce a function that lets us embed tests in this source file, choosing to run the tests by passing a `--self-test` command line argument.
// For the underlying tests, we leverage the [tape](https://github.com/substack/tape) library, which outputs test results in the [Test Anything Protocol](https://en.wikipedia.org/wiki/Test_Anything_Protocol) (TAP) format.

function testfn(fn, testImpl) {
    if (process.argv.includes('--self-test')) {
        tape(fn.name, t => testImpl(t, fn));
    }
}

// Every boolean formula can be expressed as a a conjunction of disjunctions (AKA [conjunctive normal form](https://en.wikipedia.org/wiki/Conjunctive_normal_form), or CNF) , and by constraining our solver to input in that form, we can avoid tokenizing, parsing (which includes handling operator precedence), and writing logic for redundant operators like logical implication.
//
// For example, the initial example
//
// (x1 &rArr; x2) &and; (x1 &or; &sim;x3)
//
// could be converted to CNF as
//
// (&sim; x1 &or; x2) &and; (x1 &or; &sim;x3)
//
// which would be encoded as
//
//     [{x1: false, x2: true}, // clause 1
//      {x1: true, x3: false}] // clause 2
//
// So our SAT solver `solve` accepts an array of clauses, where every clause must be satisfied, and to satisfy a clause at least one of the literals must match the associated value. With this in mind, we can implement our primary test.

testfn(solve, (t, fn) => {
    const unsatisfiable = [
        [{a: true}, {a: false}],
        [{a: true, b: false}, {b: true}, {a: false}],
    ];
    for (const problem of unsatisfiable) {
        const assignment = fn(problem);
        t.deepEqual(assignment, null);
    }

    const satisfiable = [
        [{a: false}],
        [{a: true}],
        [{a: true, b: true}, {b: true}],
        [{a: true, b: true}, {b: false}],
        [{a: true, b: true}, {a: false, b: false}],
        [{a: true, b: true, c: false}, {a: false, b: false}, {b: true, c: false}],
        [{a: true, b: true, c: false}, {a: false, b: false}, {b: true, c: true}],
        [{a: true, b: false, c: false}, {a: false, b: false}, {b: true, c: true}],
        [{a: true, b: true}, {b: true, c: true}],
        [{a: false, b: true}, {b: false}, {c: false, b: true}],
    ];
    for (const problem of satisfiable) {
        const assignment = fn(problem);
        t.ok(!!assignment);
        const isValidAssignment = problem.every(clause => {
            const isSatisfied = Object.keys(clause).some(atom => clause[atom] === assignment[atom]);
            return isSatisfied;
        });
        t.ok(isValidAssignment);
    }

    t.end();
});

//
// ## Solver Implementation ##
//

// Many SAT algorithms exist, and one of the most fundamental is [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm):
//
// 1. `nextVar`: choose a variable favoring "unit" clauses with only one possible assignment;
// 2. `canAssign`: infer when an assignment of that variable violates any clause;
// 3. `removeVar`: "clean up" satisfied clauses; and
// 4. `newAssignment`: update a collection of assignments (which can be unwound by backtracking when all possible assignments of a variable lead to a clause violation).
//
// We start by introducing a helper for each of the above steps.

testfn(nextVar, (t, fn) => {
    t.deepEqual(fn([]), null);
    t.deepEqual(fn([{}]), null);
    t.deepEqual(fn([{x: 0}]), 'x');
    t.deepEqual(fn([{x: 0, y: 0}]), 'x');
    t.end();
});
function nextVar(clauses) {
    const clauseKeys = clauses.map(c => Object.keys(c));
    if (clauseKeys.some(c => c.length == 0)) {
        return null;
    }
    const unit = clauseKeys.find(c => c.length == 1);
    if (unit) {
        return unit[0];
    }
    return clauseKeys.reduce((l, r) => l.concat(r), []).find(x => x) || null;
}

testfn(canAssign, (t, fn) => {
    t.deepEqual(fn(true, 'x', []), true);
    t.deepEqual(fn(true, 'x', [{}]), true); // NOTE: clause is unsat, but assignment is valid

    t.deepEqual(fn(true, 'x', [{y: true}]), true);
    t.deepEqual(fn(true, 'x', [{y: false}]), true);

    t.deepEqual(fn(true, 'x', [{x: true}]), true);
    t.deepEqual(fn(true, 'x', [{x: false}]), false);
    t.end();
});
function canAssign(value, variable, clauses) {
    return clauses.every(c => Object.keys(c).length > 1 || !c.hasOwnProperty(variable) || c[variable] == value);
}

testfn(removeVar, (t, fn) => {
    t.deepEqual(
        fn(true, 1, [{1: false, 3: true}, {2: false}, {2: true, 3: false}]),
        [{3: true}, {2: false}, {2: true, 3: false}]);
    t.deepEqual(
        fn(false, 1, [{1: false, 3: true}, {2: false}, {2: true, 3: false}]),
        [{2: false}, {2: true, 3: false}]);
    t.end();
});
function removeVar(value, variable, clauses) {
    return clauses.filter(c => c[variable] !== value).map(c => {
        const result = Object.assign({}, c);
        delete result[variable];
        return result;
    });
}

testfn(newAssignment, (t, fn) => {
    t.deepEqual(
        newAssignment({}, 'x', true),
        {x: true});
    t.deepEqual(
        newAssignment({}, 'y', false),
        {y: false});
    t.deepEqual(
        newAssignment({x: false}, 'y', true),
        {x: false, y: true});
    t.end();
});
function newAssignment(original, variable, value) {
    const result = Object.assign({}, original);
    result[variable] = value;
    return result;
}

// Now we can bring those pieces together to implement the DPLL algorithm.

function solve(clauses, assignment = {}) {
    return trace(solve, arguments, () => { // we wrap in a helper for debugging
        const v = nextVar(clauses);
        if (!v) { return assignment; }
        if (canAssign(true, v, clauses)) {
            const result = solve(removeVar(true, v, clauses), newAssignment(assignment, v, true));
            if (result) {
                return result;
            }
        }
        if (canAssign(false, v, clauses)) {
            const result = solve(removeVar(false, v, clauses), newAssignment(assignment, v, false));
            if (result) {
                return result;
            }
        }
        return null;
    });
}

//
// ## Parsing ##
//
// The [DIMACS CNF format](http://people.sc.fsu.edu/~jburkardt%20/data/cnf/cnf.html) specifies a common encoding for CNF expressions.
// By parsing this format, we can validate our implemenation against more test data and also easily compare our SAT performance with other implementations.

testfn(parseDimacs, (t, fn) => {
    const example = `
c  simple_v3_c2.cnf
c
p cnf 3 2
1 -3 0
2 3 -1 0
`;
    t.deepEqual(
        parseDimacs(example),
        [{x1: true, x3: false}, {x1: false, x2: true, x3: true}]);
    t.end();
});
function parseDimacs(data) {
    // First we remove comments, which are lines starting with a "c" character.
    data = data.replace(/(^|\n)c.*/g, '');

    // Next we extract the problem description, which indicates the number of symbols and clauses.
    // For simplicity, we just throw this away as we can infer it from the rest of the file.
    const lines = data.replace(/(^|\n)c.*/g, '').split('\n');
    let i = 0;
    while (lines[i].length == 0 || lines[i][0] != 'p') { ++i; }
    const problem = lines[i].match(/\S+/g);
    debug({problem});

    // Now we are ready to extract the clauses. Note that clauses are "0" delimited, not newline delimited.
    const clauses = lines.splice(i+1) // start w/ lines after the problem
        .join('\n').split(/\s+0/)     // split on '0' character delimiter instead of newline
        .map(l => l.match(/\S+/g))    // extract tokens
        .filter(l => l);              // and filter out noise
    debug({clauses});

    // The clauses are encoded such that `-num` indicates that x<sub>num</sub> is false while `num` indicates x<sub>num</sub> is true.
    return clauses.map(encoded => {
        const decoded = {};
        for (const sym of encoded) {
            if (sym < 0) {
                decoded['x' + -sym] = false;
            } else {
                decoded['x' + sym] = true;
            }
        }
        return decoded;
    });
}

//
// # Performance #
//
// Similar to our `testfn` helper, we introduce a `timefn` helper that only runs performance tests if the program is started with a `--perf` argument.

function timefn(fn, impl) {
    const count = 1;

    if (!process.argv.includes('--perf')) { return; }

    console.log(`# ${fn.name}`);
    impl(fn, (description, computation) => {
        const start = new Date();
        for (let i = 0; i < count; ++i) {
            computation();
        }
        const end = new Date();
        console.log(`## ${description}: ${(end - start)/count} ms`);
    });
}

// To stress our solver a bit, we have three example DIMACS CNF files:
// 1. [aim-50-1_6-yes1-4.cnf](http://people.sc.fsu.edu/~jburkardt/data/cnf/aim-50-1_6-yes1-4.cnf)
// 2. [aim-100-1_6-no-1.cnf](http://people.sc.fsu.edu/~jburkardt/data/cnf/aim-100-1_6-no-1.cnf)
// 3. [zebra_v155_c1135.cnf](http://people.sc.fsu.edu/~jburkardt%20/data/cnf/zebra_v155_c1135.cnf)

timefn(solve, (fn, time) => {
    fs.readFile('aim-50-1_6-yes1-4.cnf', 'utf-8', (err, data) => {
        const constraints = parseDimacs(data);
        time('aim-50-1_6-yes1-4.cnf: satisfiable', () => solve(constraints));
    });
    fs.readFile('aim-100-1_6-no-1.cnf', 'utf-8', (err, data) => {
        const constraints = parseDimacs(data);
        time('aim-100-1_6-no-1.cnf: unsatisfiable', () => solve(constraints));
    });
    fs.readFile('zebra_v155_c1135.cnf', 'utf-8', (err, data) => {
        const constraints = parseDimacs(data);
        time('zebra_v155_c1135.cnf: satisfiable', () => solve(constraints));
    });
});

// Two of the problems are satisfiable and take just under a second on my laptop, while one is unsatisfiable and takes just over a minute on the same hardware.
// For comparison, the industrial strength [Z3](https://github.com/Z3Prover/z3) theorem prover can solve all three in milliseconds.
// It's clear that this minimal example has lots of room for performance improvements!

//
// ## Appendix: Development Helpers ##
//
// TAP parsers expect a leading `#` for comments, and outputing debug information to the console without that leading `#` breaks parsing.
// To make our debug logging slightly less verbose, we introduce another small helper, `debug`.
//
// Note that while `#` indicates a comment, nodejs TAP reporters (such as [tap-spec](https://github.com/scottcorgan/tap-spec)) typically interpret `#` as a test name, so this helper emits a `##`, which most parsers interpret as a non-test-comment.

function debug(format, ... other) {
    if (process.argv.includes('--debug')) {
        if (typeof format != 'string') {
            format = util.inspect(format);
        }
        console.log('## ' + format, ...other);
    }
}

// It's also useful to be able to trace function calls, so we introduce a helper for that as well.
// Example output:
//     ## solve <-- [ { a: true, b: true }, { b: true } ]
//     ##     solve <-- [ { b: true } ], { a: true }
//     ##         solve <-- [], { a: true, b: true }
//     ##         solve --> { a: true, b: true }
//     ##     solve --> { a: true, b: true }
//     ## solve --> { a: true, b: true }

function trace(fn, args, impl) {
    if (!process.argv.includes('--debug')) { return impl.apply(this, args); }

    trace.depth = trace.depth || 0;

    const pad = '    '.repeat(trace.depth);
    const name = fn.name || new Error().stack.match(/ at ([^ ]+)/g)[1].split(' ')[2];
    try {
        ++trace.depth;

        debug(`${pad}${name} <--`, Array.from(args).map(util.inspect).join(', '));
        const result = impl.apply(this, args);
        debug(`${pad}${name} -->`, result);

        return result;
    } catch(err) {
        debug(`${pad}${name} !!!`, err);
        throw err;
    } finally {
        --trace.depth;
    }
}
