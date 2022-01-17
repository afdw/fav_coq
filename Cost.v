From Ltac2 Require Import Ltac2.
From Ltac2 Require Message.
From Ltac2 Require Import Printf.
From Ltac2 Require Constr.

Set Default Proof Mode "Classic".
Set Ltac2 Backtrace.

Ltac2 rec string_to_list s :=
  let rec aux s i :=
    if Int.equal (String.length s) i
    then []
    else (String.get s i) :: (aux s (Int.add i 1)) in
  aux s 0.

Ltac2 string_of_list l :=
  let s := String.make (List.length l) (String.get " " 0) in
  let _ := List.mapi (fun i c => String.set s i c) l in
  s.

Ltac2 string_concat s t :=
  string_of_list (List.append (string_to_list s) (string_to_list t)).

Module Cost.

Ltac2 cost_sum a_cost b_cost :=
  Constr.Unsafe.make (Constr.Unsafe.App 'plus (Array.of_list ([a_cost; b_cost]))).

Ltac2 add_const_to_cost_fun cost_fun additional_cost depth :=
  let rec sum_fun depth :=
    if Int.equal depth 0
    then
      Constr.Unsafe.make (
        Constr.Unsafe.Lambda
        (Constr.Binder.make (Some @x) '(_ : Type))
        (Constr.Unsafe.make (
          Constr.Unsafe.Lambda
          (Constr.Binder.make (Some @y) '(_ : Type))
          (cost_sum (Constr.Unsafe.make (Constr.Unsafe.Rel 2)) (Constr.Unsafe.make (Constr.Unsafe.Rel 1)))
        ))
      )
    else
      Constr.Unsafe.make (
        Constr.Unsafe.Lambda
        (Constr.Binder.make (Some @x) '(_ : Type))
        (Constr.Unsafe.make (
          Constr.Unsafe.Lambda
          (Constr.Binder.make (Some @y) '(_ : Type))
          (Constr.Unsafe.make (
            Constr.Unsafe.Lambda
            (Constr.Binder.make (Some @z) '(_ : Type))
            (Constr.Unsafe.make (
              Constr.Unsafe.App
              (sum_fun (Int.sub depth 1))
              (Array.of_list [
                Constr.Unsafe.make (
                  Constr.Unsafe.App
                  (Constr.Unsafe.make (Constr.Unsafe.Rel 3))
                  (Array.of_list [Constr.Unsafe.make (Constr.Unsafe.Rel 1)])
                );
                Constr.Unsafe.make (Constr.Unsafe.Rel 2)
              ])
            ))
          ))
        ))
      )
    in
  Constr.Unsafe.make (Constr.Unsafe.App (sum_fun depth) (Array.of_list ([cost_fun; additional_cost]))).

Ltac2 rec count_lambda_depth constr :=
  match Constr.Unsafe.kind constr with
  | Constr.Unsafe.Lambda args body => Int.add (count_lambda_depth body) 1
  | _ => 0
  end.

Ltac2 rec to_prod_nat type_constr i n :=
  if Int.equal i n
  then 'nat
  else
    match Constr.Unsafe.kind type_constr with
    | Constr.Unsafe.Prod param body =>
      Constr.Unsafe.make (Constr.Unsafe.Prod param (to_prod_nat body (Int.add i 1) n))
    | _ =>
      printf "Warning: compute_time can not handle fixpoint with non-prod type";
      type_constr
    end.

Ltac2 rec is_constant_one constr :=
  Bool.or
    (Constr.equal constr '1)
    (match Constr.Unsafe.kind constr with
    | Constr.Unsafe.Lambda args body => is_constant_one body
    | _ => false
    end).

Inductive __compute_cost_fix_pair {S T : Type} :=
  | __compute_cost_fix_pair_value : S -> T -> _.

Definition __compute_cost_fix_pair_fst {S T} (p : @__compute_cost_fix_pair S T) :=
  match p with
  | __compute_cost_fix_pair_value x _ => x
  end.

Ltac2 rec join_replace replacements a_constr b_constr :=
  printf "Trace: join_replace _ %t %t" a_constr b_constr;
  match Constr.Unsafe.kind a_constr with
  | Constr.Unsafe.Rel rel =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.Rel _ => a_constr
    | Constr.Unsafe.Var var =>
      Constr.Unsafe.make (
        Constr.Unsafe.App
        '@__compute_cost_fix_pair_fst
        (Array.of_list [
          '_;
          '_;
          Constr.Unsafe.make (
            Constr.Unsafe.App
            '@__compute_cost_fix_pair_value
            (Array.of_list [
              '_;
              '_;
              List.assoc Ident.equal var replacements;
              a_constr
            ])
          )
        ])
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.Var _ => a_constr
  | Constr.Unsafe.Evar evar a_args =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.Evar evar b_args =>
      Constr.Unsafe.make (
        Constr.Unsafe.Evar
        evar
        (Array.map2 (join_replace replacements) a_args b_args)
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.Sort _ => a_constr
  | Constr.Unsafe.Prod arg a_u =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.Prod _ b_u =>
      Constr.Unsafe.make (
        Constr.Unsafe.Prod
        arg
        (join_replace replacements a_u b_u)
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.Lambda arg a_body =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.Lambda arg b_body =>
      Constr.Unsafe.make (
        Constr.Unsafe.Lambda
        arg
        (join_replace replacements a_body b_body)
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.LetIn b a_t a_c =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.LetIn b b_t b_c =>
      Constr.Unsafe.make (
        Constr.Unsafe.LetIn
        b
        (join_replace replacements a_t b_t)
        (join_replace replacements a_c b_c)
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.Ind _ _ => a_constr
  | Constr.Unsafe.Constructor _ _ => a_constr
  | Constr.Unsafe.Case ci a_c iv a_t a_bl =>
    match iv with
    | Constr.Unsafe.NoInvert => ()
    | Constr.Unsafe.CaseInvert _ =>
      printf "Warning: compute_time can not handle match with CaseInvert; what it even means?"
    end;
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.Case ci b_c iv b_t b_bl =>
      Constr.Unsafe.make (
        Constr.Unsafe.Case
        ci
        (join_replace replacements a_c b_c)
        iv
        (join_replace replacements a_t b_t)
        (Array.map2 (join_replace replacements) a_bl b_bl)
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.Fix recs i nas a_cs =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.Fix recs i nas b_cs =>
      Constr.Unsafe.make (
        Constr.Unsafe.Fix
        recs
        i
        nas
        (Array.map2 (join_replace replacements) a_cs b_cs)
      )
    | _ => Control.throw Match_failure
    end
  | Constr.Unsafe.Constant _ _ => a_constr
  | Constr.Unsafe.App a_fun a_args =>
    match Constr.Unsafe.kind b_constr with
    | Constr.Unsafe.App b_fun b_args =>
      Constr.Unsafe.make (
        Constr.Unsafe.App
        (join_replace replacements a_fun b_fun)
        (Array.map2 (join_replace replacements) a_args b_args)
      )
    | _ => Control.throw Match_failure
    end
  | _ => Control.throw Match_failure
  end.

Ltac2 rec compute_cost cost_functions depth input_constr :=
  printf "Trace: compute_time _ %i %t" depth input_constr;
  let pair_equal :=
    (fun (a_constr, a_depth) (b_constr, b_depth) =>
      Bool.and (Constr.equal a_constr b_constr) (Int.equal a_depth b_depth)
    ) in
  let result_constr :=
    match List.assoc_opt pair_equal (input_constr, depth) cost_functions with
    | Some result_constr => result_constr
    | None =>
      match Constr.Unsafe.kind input_constr with
      | Constr.Unsafe.Lambda _ _ => ()
      | Constr.Unsafe.App _ _ => ()
      | Constr.Unsafe.Fix _ _ _ _ => ()
      | Constr.Unsafe.Constant _ _ => ()
      | _ =>
        if Int.equal depth 0
        then ()
        else printf "Warning: compute_time expects depth to be 0 at this point"
      end;
      match Constr.Unsafe.kind input_constr with
      | Constr.Unsafe.Rel _ => '1
      | Constr.Unsafe.Var _ => '1
      | Constr.Unsafe.Evar _ _ => printf "Warning: compute_time assumes that evars are constant-time"; '1
      | Constr.Unsafe.Sort _ => '1
      | Constr.Unsafe.Prod _ _ => '1
      | Constr.Unsafe.Lambda arg body =>
        if Int.equal depth 0
        then '1
        else
          let body_cost := compute_cost cost_functions (Int.sub depth 1) body in
          Constr.Unsafe.make (Constr.Unsafe.Lambda arg body_cost)
      | Constr.Unsafe.LetIn b t c =>
        let t_cost := compute_cost cost_functions 0 t in
        let c_cost := Constr.Unsafe.make (Constr.Unsafe.LetIn b t (compute_cost cost_functions 0 c)) in
        cost_sum t_cost c_cost
      | Constr.Unsafe.Constructor _ _ => '1
      | Constr.Unsafe.Ind _ _ => '1
      | Constr.Unsafe.Case ci c iv t bl =>
        let t_cost := compute_cost cost_functions 0 t in
        let c_replacement := match Constr.Unsafe.kind c with
        | Constr.Unsafe.Lambda arg body => Constr.Unsafe.make (Constr.Unsafe.Lambda arg 'nat)
        | _ => printf "Warning: compute_time can not handle match with non-lambda 'c'"; c
        end in
        match iv with
        | Constr.Unsafe.NoInvert => ()
        | Constr.Unsafe.CaseInvert _ =>
          printf "Warning: compute_time can not handle match with CaseInvert; what it even means?"
        end;
        let bl_costs := Array.map (fun b =>
          compute_cost cost_functions (Int.add depth (count_lambda_depth b)) b
        ) bl in
        let branches_cost :=
          if Array.for_all is_constant_one bl_costs
          then '1
          else Constr.Unsafe.make (Constr.Unsafe.Case ci c_replacement iv t bl_costs) in
        add_const_to_cost_fun branches_cost t_cost depth
      | Constr.Unsafe.Fix recs i nas cs =>
        let nas_replacements := Array.mapi (fun j binder =>
          Constr.Binder.make
            (
              Option.map
              (fun ident =>
                Option.get (Ident.of_string (string_concat (Ident.to_string ident) "_cost"))
              )
              (Constr.Binder.name binder)
            )
            (to_prod_nat (Constr.Binder.type binder) 0 depth)
        ) nas in
        let cs_costs := Array.mapi (fun k c =>
          let idents :=
            List.fold_right (fun _ prev_idents =>
              List.append prev_idents [Fresh.fresh (Fresh.Free.of_ids prev_idents) @__compute_cost_fix_ident]
            ) [] (Array.to_list nas) in
          printf "Trace: compute_time, fix %i: had %t" k c;
          let c_subst :=
            Constr.Unsafe.substnl
            (List.map (fun ident => Constr.Unsafe.make (Constr.Unsafe.Var ident)) idents)
            0
            c in
          printf "Trace: compute_time, fix %i: after substitution got %t" k c_subst;
          let c_joined :=
            join_replace
            (List.mapi (fun j ident => (ident, Constr.Unsafe.make (Constr.Unsafe.Fix recs j nas cs))) idents)
            c
            c_subst in
          printf "Trace: compute_time, fix %i: after joining got %t" k c_joined;
          compute_cost cost_functions depth c_joined
        ) cs in
        Constr.Unsafe.make (Constr.Unsafe.Fix recs i nas_replacements cs_costs)
      | Constr.Unsafe.Constant _ _ =>
        let red_expr := eval red in $input_constr in
        compute_cost cost_functions depth red_expr
      | Constr.Unsafe.App fun_ args =>
        let real_args :=
          if Constr.equal fun_ '@__compute_cost_fix_pair_fst
          then Array.sub args 3 (Int.sub (Array.length args) 3)
          else args in
        let fun_cost :=
          if Constr.equal fun_ '@__compute_cost_fix_pair_fst
          then
            match Constr.Unsafe.kind (Array.get args 2) with
            | Constr.Unsafe.App _ inner_args =>
              let cost_fun := Array.get inner_args 3 in
              Constr.Unsafe.make (Constr.Unsafe.App cost_fun real_args)
            | _ => Control.throw Match_failure
            end
          else
            match Constr.Unsafe.kind fun_ with
            | Constr.Unsafe.Ind _ _ => '1
            | Constr.Unsafe.Constructor _ _ => '1
            | _ =>
              let replaced_cost :=
                List.fold_right
                (fun i prev =>
                  match prev with
                  | None =>
                    let to_be_replaced_fun :=
                      let to_be_replaced_args := Array.sub args 0 i in
                      Constr.Unsafe.make (Constr.Unsafe.App fun_ to_be_replaced_args) in
                    match
                      List.assoc_opt
                      pair_equal
                      (to_be_replaced_fun, Int.sub (Array.length args) i)
                      cost_functions
                    with
                    | Some replaced_fun =>
                      printf "Trace: compute_time found a replacement";
                      let replaced_args := Array.sub args i (Int.sub (Array.length args) i) in
                      Some (Constr.Unsafe.make (Constr.Unsafe.App replaced_fun replaced_args))
                    | None => None
                    end
                  | Some cost => Some cost
                  end
                )
                None
                (List.mapi (fun i _ => i) (Array.to_list real_args)) in
              match replaced_cost with
              | None =>
                let cost_fun := compute_cost cost_functions (Int.add depth (Array.length args)) fun_ in
                Constr.Unsafe.make (Constr.Unsafe.App cost_fun args)
              | Some cost => cost
              end
            end in
        let args_costs := Array.map (compute_cost cost_functions 0) real_args in
        let args_cost := Array.fold_left cost_sum '0 args_costs in
        add_const_to_cost_fun fun_cost args_cost depth
      | _ => Control.throw Match_failure
      end
    end in
  printf "Trace:            ^- %t" result_constr;
  result_constr.

Ltac2 mutable registered_cost_functions : unit -> ((constr * int) * constr) list := fun () => [].

Ltac2 refine_compute_cost cost_functions depth input_constr folds :=
  Control.refine (fun () =>
    let result_constr :=
      compute_cost
      (List.append cost_functions (registered_cost_functions ()))
      depth
      input_constr in
    let simplified_constr := eval simpl in $result_constr in
    Std.eval_fold folds simplified_constr
  ).

Section Example.

Definition mul_cost := ltac2:(refine_compute_cost [] 2 'Nat.mul ['Nat.mul]).

End Example.

Ltac2 default_registered_cost_functions () :=
  [
    (('plus, 2), '(fun (_ _ : nat) => 1));
    (('Nat.mul, 2), '(fun (_ _ : nat) => 1))
  ].
Ltac2 Set registered_cost_functions := fun () => default_registered_cost_functions ().

Section Example.

Fixpoint nat_id n :=
  match n with
  | 0 => 0
  | S n' => S (nat_id n')
  end.

Definition nat_id_cost := ltac2:(refine_compute_cost [] 1 'nat_id []).

Fixpoint is_even n :=
  match n with
  | 0 => true
  | S n' => negb (negb (is_odd n'))
  end
with is_odd n :=
  match n with
  | 0 => false
  | S n' => is_even n'
  end.

Definition is_even_cost := ltac2:(refine_compute_cost [] 1 'is_even ['is_even; 'is_odd]).

Fixpoint factorial n :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.

Definition factorial_cost := ltac2:(refine_compute_cost [] 1 'factorial []).

Definition filter {T} (predicate : T -> bool) :=
  fix filter (list : list T) :=
    match list with
    | nil => nil
    | cons element list' =>
      if predicate element
      then cons element (filter list')
      else filter list'
    end.

Definition filter_cost {T} predicate predicate_cost :=
  ltac2:(refine_compute_cost [(('predicate, 1), 'predicate_cost)] 1 (eval red in (@filter T predicate)) []).

Compute filter_cost (fun x => true) (fun x => 1) (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil).

End Example.

End Cost.
