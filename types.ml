(* *************************** DEFINITIONS *************************** *)

(* 
   Syntax
   -------
   Represents the abstract syntax of typs using De Bruijn indices for variables.
*)
type term =
  | Var of int
  | Star
  | Pi of term * term
  | Fun of term * term
  | App of term * term
  | Nat
  | Zero
  | Succ of term
  | ElimNat of term * term * term * term

module VarSet = Set.Make(Int)

(* 
   Term Equality
   --------------
   Checks structural equality between two terms.
*)
let rec term_beq t1 t2 =
  match t1, t2 with
  | Var n1, Var n2 -> n1 = n2
  | Star, Star -> true
  | Pi (tx, tx'), Pi (ty, ty')
  | Fun (tx, tx'), Fun (ty, ty') ->
      term_beq tx ty && term_beq tx' ty'
  | App (t11, t12), App (t21, t22) ->
      term_beq t11 t21 && term_beq t12 t22
  | Nat, Nat
  | Zero, Zero -> true
  | Succ t1', Succ t2' -> term_beq t1' t2'
  | ElimNat (t1, t2, t3, t4), ElimNat (t5, t6, t7, t8) ->
      term_beq t1 t5 && term_beq t2 t6 && term_beq t3 t7 && term_beq t4 t8
  | _, _ -> false

(* 
   Convert Nat to Term
   -------------------
   Transforms a natural number into its corresponding `term` representation.
*)
let rec nat_to_term n =
  if n = 0 then Zero else Succ (nat_to_term (n - 1))

(* 
   Convert Term to Nat - Only for Examples.
   -------------------
   Attempts to convert a `term` back into a natural number.
   Returns `None` if the term does not represent a natural number.
*)
let rec term_to_nat t =
  match t with
  | Zero -> Some 0
  | Succ t' ->
      (match term_to_nat t' with
      | Some n -> Some (n + 1)
      | None -> None)
  | _ -> None


(* 
   Free Variables
   ------------------
   Finds the string set of free variables in an expression/term
*)
let rec free_vars (t : term) (bound : VarSet.t) : VarSet.t =
  match t with
  | Var x -> 
      if VarSet.mem x bound then VarSet.empty else VarSet.singleton x
  | Star | Nat | Zero -> 
      VarSet.empty
  | Succ t' -> 
      free_vars t' bound
  | Pi (t1, t2) 
  | Fun (t1, t2) -> 
      VarSet.union (free_vars t1 bound) (free_vars t2 bound)
  | App (t1, t2) -> 
      VarSet.union (free_vars t1 bound) (free_vars t2 bound)
  | ElimNat (t1, t2, t3, t4) -> 
      VarSet.union (free_vars t1 bound)
        (VarSet.union (free_vars t2 bound)
           (VarSet.union (free_vars t3 bound) (free_vars t4 bound)))
  | _ -> VarSet.empty

(* 
   De Bruijn Lifting
   ------------------
   Increments variable indices in a term to account for introducing new bindings.
*)
let rec lift n k t =
  match t with
  | Var x ->
      if x < k then Var x else Var (x + n)
  | Star -> Star
  | Pi (ty, t') ->
      Pi ((lift n k ty), (lift n (k + 1) t'))
  | Fun (ty, t') ->
      Fun ((lift n k ty), (lift n (k + 1) t'))
  | App (t1, t2) ->
      App ((lift n k t1), (lift n k t2))
  | Nat -> Nat
  | Zero -> Zero
  | Succ t' ->
      Succ (lift n k t')
  | ElimNat (t1, t2, t3, t4) ->
      ElimNat ((lift n k t1), (lift n k t2), (lift n k t3), (lift n k t4))

(* 
   De Bruijn Substitution *****
   -----------------------
   Substitutes the `n`-th variable in term `t` with the replacement term `repl`.
*)
let rec subst n repl t =
  match t with
  | Var x ->
      if x = n then repl
      else if x < n then Var x
      else Var (x - 1)
  | Star -> Star
  | Pi (ty, t') ->
      Pi ((subst n repl ty), (subst (n + 1) (lift 1 0 repl) t'))
  | Fun (ty, t') ->
      Fun ((subst n repl ty), (subst (n + 1) (lift 1 0 repl) t'))
  | App (t1, t2) ->
      App ((subst n repl t1), (subst n repl t2))
  | Nat -> Nat
  | Zero -> Zero
  | Succ t' ->
      Succ (subst n repl t')
  | ElimNat (t1, t2, t3, t4) ->
      ElimNat ((subst n repl t1), (subst n repl t2), (subst n repl t3), (subst n repl t4))

(* 
   Evaluation
   ----------
   Evaluates a term to its normal form.
*)
let rec eval t =
  match t with
  | Var n -> Var n
  | Star -> Star
  | Pi (ty, t') ->
      Pi ((eval ty), (eval t'))
  | Fun (ty, t') ->
      Fun ((eval ty), (eval t'))
  | App (t1, t2) ->
      let t1' = eval t1 in
      let t2' = eval t2 in
      (match t1' with
      | Fun (_, t') -> subst 0 t2' t'
      | _ -> App (t1', t2'))
  | Nat -> Nat
  | Zero -> Zero
  | Succ t' -> 
      Succ (eval t')
  | ElimNat (t1, t0, tsuc, t') ->
      let t'' = eval t' in
      (match t'' with
      | Zero -> eval t0
      | Succ n -> App ((App (tsuc, n)), (ElimNat (t1, t0, tsuc, n)))
      | _ -> ElimNat ((eval t1), (eval t0), (eval tsuc), t''))

(* Draw out an example tree *)

(* 
   Evaluation with Fuel
   ---------------------
   Evaluates a term with a limited number of evaluation steps to prevent non-typination.
*)
let rec eval_fuel n t =
  if n = 0 then t
  else eval_fuel (n - 1) (eval t)

(* 
   Typing Relation
   ---------------
   Detypines the type of a term within a given context.
   Returns `Some type` if well-typed, otherwise `None`.
*)
let rec get_type envt t =
  match t with
  | Var n -> List.nth_opt envt n
  | Star -> Some Star
  | Pi (ty, t') ->
      (match get_type envt ty, get_type (ty :: envt) t' with
      | Some Star, Some Star -> Some Star
      | _, _ -> None)
  | Fun (ty, t') ->
      (match get_type (ty :: envt) t' with
      | Some ty2 ->
          (match get_type envt ty with
          | Some Star -> Some (Pi (ty, ty2))
          | _ -> None)
      | None -> None)
  | App (t1, t2) ->
      (match get_type envt t1, get_type envt t2 with
      | Some (Pi (ty, t')), Some ty' ->
          if term_beq ty ty' then Some (subst 0 t2 t') else None
      | _, _ -> None)
  | Nat -> Some Star
  | Zero -> Some Nat
  | Succ t' ->
      (match get_type envt t' with
      | Some Nat -> Some Nat
      | _ -> None)
  | ElimNat (t1, t0, tsuc, t') ->
      let ty = eval (App (t1, Zero)) in
      (match get_type envt t1, get_type envt t0, get_type envt tsuc, get_type envt t' with
      | Some (Pi (Nat, Star)), Some ty1, Some (Pi (Nat, Pi (ty2, ty3))), Some Nat ->
          if (term_beq ty ty1) && (term_beq ty ty2) && (term_beq ty ty3) then Some ty else None
      | _, _, _, _ ->
          None)

(* *************************** EXAMPLES *************************** *)

(* 
   Substitution Example
   ---------------------
   Fun.((1 (Fun.3)) 2)[1 <- 0] = Fun.((1 (Fun.2)) 1)
*)
let subst1 =
  let original = Fun (Nat,
                      App (App ((Var 1), (Fun (Nat, Var 3))),
                        Var 2))
  in
  let expected = Fun (Nat,
                      App (App ((Var 1), (Fun (Nat, Var 2))),
                        Var 1))
  in
  let result = subst 1 (Var 0) original in
  assert (term_beq result expected)

(* 
   Evaluation Example
   ------------------
   ((Fun.Fun.1) Succ Succ Zero) Zero = Succ Succ Zero
*)
let eval1 =
  let term = App (
               App ((Fun (Nat, Fun (Nat, Var 1))),
                 (Succ (Succ Zero))),
               Zero)
  in
  let expected = Succ (Succ Zero) in
  let result = eval term in
  assert (term_beq result expected)

(* 
   Omega Combinator - helped by GPT, understood in post!
   -----------------
   omega = App (Fun Nat (App (Var 0) (Var 0))) (Fun Nat (App (Var 0) (Var 0)))
   Evaluating omega should result in omega itself.
*)
let omega =
  App (
    Fun (Nat, App ((Var 0), (Var 0))),
    Fun (Nat, App ((Var 0), (Var 0)))
  )

let omega1 =
  let result = eval omega in
  assert (term_beq result omega)

(* 
   Polymorphic Identity Function
   -----------------------------
   id = Fun Star (Fun (Var 0) (Var 0))
*)
let id =
  Fun (Star, Fun (Var 0, Var 0))

(* 
   id1: Fun.Succ 0 = Fun.Succ 0
*)
let id1 =
  let term = App ((App (id, (Pi (Nat, Nat)))), (Fun (Nat, Succ (Var 0)))) in
  let expected = Fun (Nat, Succ (Var 0)) in
  let result = eval term in
  assert (term_beq result expected)

(* 
   Addition Function
   --------------
   plus = Fun Nat (Fun Nat (ElimNat (Fun Nat Nat) (Var 1) (Fun Nat (Fun Nat (Succ (Var 0)))) (Var 0)))
*)
let plus =
  Fun (Nat,
       Fun (Nat,
            ElimNat (
              Fun (Nat, Nat),
              Var 1,
              Fun (Nat, Fun (Nat, Succ (Var 0))),
              Var 0)))

(* 
   plus1: 10 + 0 = 10
*)
let plus1 =
  let term = App ((App (plus, (nat_to_term 10))), Zero) in
  let expected = nat_to_term 10 in
  let result = eval_fuel 25 term in
  assert (term_beq result expected)

(* 
   plus2: 13 + 25 = 38
*)
let plus2 =
  let term = App ((App (plus, (nat_to_term 13))), (nat_to_term 25)) in
  let expected = nat_to_term 38 in
  let result = eval_fuel 50 term in
  assert (term_beq result expected)

(* 
   plus3: plus : Nat -> Nat -> Nat
*)
let plus3 =
  let expected = Some (Pi (Nat, Pi (Nat, Nat))) in
  let result = get_type [] plus in
  assert (match result, expected with
          | Some t1, Some t2 -> term_beq t1 t2
          | _ -> false)

(* 
   Run All Tests
   -------------
   Execute all example tests to verify correctness.
*)
let () =
  subst1;
  subst1;
  eval1;
  omega1;
  id1;
  plus1;
  plus2;
  plus3;
  print_endline "All tests passed successfully."