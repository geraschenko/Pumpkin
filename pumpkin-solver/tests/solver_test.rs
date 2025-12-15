#![cfg(test)] // workaround for https://github.com/rust-lang/rust-clippy/issues/11024

use std::path::PathBuf;

use pumpkin_solver::Solver;
use pumpkin_solver::constraints;
use pumpkin_solver::constraints::NegatableConstraint;
use pumpkin_solver::constraints::binary_less_than;
use pumpkin_solver::options::SolverOptions;
use pumpkin_solver::predicate;
use pumpkin_solver::proof::ProofLog;
use pumpkin_solver::results::SatisfactionResult;
use pumpkin_solver::termination::Indefinite;

#[test]
fn proof_with_reified_literals() {
    let mut solver = Solver::with_options(SolverOptions {
        proof_log: ProofLog::cp(&PathBuf::from("/tmp/solver_proof.drcp"), true)
            .expect("created proof"),
        ..Default::default()
    });

    let constraint_tag = solver.new_constraint_tag();
    let variable = solver.new_named_bounded_integer(1, 10, "var");
    let literal = solver.new_literal_for_predicate(predicate![variable == 5], constraint_tag);

    solver
        .add_constraint(constraints::clause(vec![literal], constraint_tag))
        .post()
        .expect("no error");

    let _ = solver
        .add_constraint(constraints::not_equals([variable], 5, constraint_tag))
        .post()
        .expect_err("unsat");

    let mut brancher = solver.default_brancher();
    let result = solver.satisfy(&mut brancher, &mut Indefinite);
    assert!(matches!(result, SatisfactionResult::Unsatisfiable(_, _)));
}

#[test]
fn proof_with_equality_unit_nogood_step() {
    let mut solver = Solver::with_options(SolverOptions {
        proof_log: ProofLog::cp(&PathBuf::from("/tmp/solver_proof.drcp"), true)
            .expect("created proof"),
        ..Default::default()
    });

    let constraint_tag = solver.new_constraint_tag();

    let x1 = solver.new_named_bounded_integer(1, 2, "x1");
    let x2 = solver.new_named_bounded_integer(1, 1, "x2");
    solver
        .add_constraint(constraints::binary_not_equals(x1, x2, constraint_tag))
        .post()
        .expect("no conflict");

    let _ = solver
        .add_constraint(constraints::less_than_or_equals([x1], 1, constraint_tag))
        .post()
        .expect_err("conflict");

    let mut brancher = solver.default_brancher();
    let result = solver.satisfy(&mut brancher, &mut Indefinite);
    assert!(matches!(result, SatisfactionResult::Unsatisfiable(_, _)));
}

/// Reproduces an unexpected panic where the solver becomes internally
/// inconsistent but post() returns Ok, then new_literal() panics.
///
/// This is problematic because:
/// 1. None of the post() calls return an error
/// 2. There's no way to check if the solver is inconsistent
/// 3. With panic='abort', catch_unwind doesn't help
#[test]
fn panic_on_new_literal() {
    let mut solver = Solver::default();
    let tag = solver.new_constraint_tag();

    // 19 variables with various domain sizes (r0 through r18)
    let r0 = solver.new_bounded_integer(0, 7);
    let r1 = solver.new_bounded_integer(0, 5);
    let r2 = solver.new_bounded_integer(0, 7);
    let r3 = solver.new_bounded_integer(0, 7);
    let r4 = solver.new_bounded_integer(0, 5);
    let r5 = solver.new_bounded_integer(0, 1);
    let r6 = solver.new_bounded_integer(0, 5);
    let r7 = solver.new_bounded_integer(0, 7);
    let r8 = solver.new_bounded_integer(0, 7);
    let r9 = solver.new_bounded_integer(0, 7);
    let r10 = solver.new_bounded_integer(0, 5);
    let r11 = solver.new_bounded_integer(0, 7);
    let r12 = solver.new_bounded_integer(0, 3);
    let r13 = solver.new_bounded_integer(0, 5);
    let r14 = solver.new_bounded_integer(0, 5);
    let r15 = solver.new_bounded_integer(0, 3);
    let r16 = solver.new_bounded_integer(0, 3);
    let r17 = solver.new_bounded_integer(0, 3);
    let r18 = solver.new_bounded_integer(0, 1);

    // 12 binary_less_than constraints
    solver.add_constraint(binary_less_than(r0, r2, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r1, r4, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r4, r6, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r2, r7, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r8, r3, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r7, r9, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r9, r8, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r14, r13, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r13, r10, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r12, r15, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r15, r17, tag)).post().unwrap();
    solver.add_constraint(binary_less_than(r17, r16, tag)).post().unwrap();

    // Helper: (v_target < v_a) OR (v_b < v_target)
    let post_below_a_or_above_b = |solver: &mut Solver, v_a, v_b, v_target, tag| {
        let a = solver.new_literal();
        binary_less_than(v_target, v_a, tag).reify(solver, a).unwrap();
        let b = solver.new_literal();
        binary_less_than(v_b, v_target, tag).reify(solver, b).unwrap();
        solver.add_clause([a.get_true_predicate(), b.get_true_predicate()], tag).unwrap();
    };

    // Helper: (v1_a < v2_a) ↔ (v1_b < v2_b)
    let post_order_consistency = |solver: &mut Solver, v1_a, v1_b, v2_a, v2_b, tag| {
        let a = solver.new_literal();
        binary_less_than(v1_a, v2_a, tag).reify(solver, a).unwrap();
        let b = solver.new_literal();
        binary_less_than(v1_b, v2_b, tag).reify(solver, b).unwrap();
        solver.add_clause([a.get_false_predicate(), b.get_true_predicate()], tag).unwrap();
        solver.add_clause([a.get_true_predicate(), b.get_false_predicate()], tag).unwrap();
    };

    // 4 order_consistency and 1 below_a_or_above_b constraints
    post_order_consistency(&mut solver, r1, r2, r6, r11, tag);
    post_order_consistency(&mut solver, r8, r10, r11, r6, tag);
    post_order_consistency(&mut solver, r5, r6, r18, r14, tag);
    post_order_consistency(&mut solver, r5, r12, r18, r16, tag);
    post_below_a_or_above_b(&mut solver, r0, r3, r11, tag);

    // At this point, the solver is internally inconsistent.
    // The next new_literal() call panics with:
    // "Variables cannot be created in an inconsistent state"
    let _next_lit = solver.new_literal();
}