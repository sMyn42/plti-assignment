open Types
(* Helper: Propositional Equality *)
let same (a : term) (b : term) : term =
  Fun (Fun (Nat, Nat), Fun (App (Var 0, a), App (Var 0, b))) (* Logical equivalence as a term *)

let refl a = same a a
let trans a b c = same a c

(* Plus Function *)
let plus =
  Fun (Nat,
       Fun (Nat,
            ElimNat (
              Fun (Nat, Nat),
              Var 1, (* Base case: x + 0 = x *)
              Fun (Nat, Fun (Nat, Succ (Var 0))), (* Inductive step *)
              Var 0)))

(* Same Under Successor *)
let same_under_suc x y =
  Fun (Nat,
       ElimNat (
         Fun (Nat, Nat),
         same (Succ x) (Succ y),
         Fun (Nat, Fun (Nat, Succ (Var 0))),
         Var 0))

(* Plus Right Zero *)
let plus_right_zero x =
  ElimNat (
    Fun (Nat, Fun (Nat, Nat)),
    refl x,
    Fun (Nat, Fun (Nat, Succ (Var 0))),
    Var 0)

(* Plus Right Successor *)
let plus_right_suc x y =
  ElimNat (
    Fun (Nat, Fun (Nat, Nat)),
    refl (App (App (plus, x), y)),
    Fun (Nat, Fun (Nat, Succ (App (App (plus, x), y)))),
    Var 0)

(* Plus Commutativity - test is failing *)
let plus_comm x y =
  ElimNat (
    Fun (Nat, Fun (Nat, Nat)),
    plus_right_zero y, (* Base case *)
    Fun (Nat,
         Fun (Nat,
              trans
                (Succ (App (App (plus, x), y)))  (* Apply successor *)
                (App (App (plus, x), Succ y))  (* Swap *)
                (same_under_suc (App (App (plus, x), y)) (App (App (plus, y), x))))),
    Var 0)

let plus_comm_test1 =
  let term = plus_comm (nat_to_term 3) (nat_to_term 2) in
  let expected = nat_to_term 5 in
  let result = eval_fuel 10 term in
  print_endline (let None = term_to_nat result in "none")

let () =
  plus_comm_test1;
  print_endline "done!"