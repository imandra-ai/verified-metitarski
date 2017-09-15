(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Isar proof reconstruction from ATP proofs.
*)

signature SLEDGEHAMMER_ISAR =
sig
  type atp_step_name = ATP_Proof.atp_step_name
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof
  type stature = ATP_Problem_Generate.stature
  type one_line_params = Sledgehammer_Proof_Methods.one_line_params

  val trace : bool Config.T

  type isar_params =
    bool * (string option * string option) * Time.time * real option * bool * bool
    * (term, string) atp_step list * thm

  val proof_text : Proof.context -> bool -> bool option -> bool option -> (unit -> isar_params) ->
    int -> one_line_params -> string

  val isar_proof_text : Proof.context -> bool -> int -> bool option -> bool option ->
    (unit -> isar_params) -> one_line_params -> string
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open ATP_Waldmeister
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay
open Sledgehammer_Isar_Compress
open Sledgehammer_Isar_Minimize

structure String_Redirect = ATP_Proof_Redirect(
  type key = atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect

(* (K true) to print the refute_graph and direct_graph *)
val trace = Attrib.setup_config_bool @{binding sledgehammer_isar_trace} (K true)

val e_definition_rule = "definition"
(*The Metitarski skolemization rule is called the same*)
val e_skolemize_rule = "skolemize"
val leo2_extcnf_forall_neg_rule = "extcnf_forall_neg"
val pirate_datatype_rule = "DT"
val satallax_skolemize_rule = "tab_ex"
val vampire_skolemisation_rule = "skolemisation"
val veriT_la_generic_rule = "la_generic"
val veriT_simp_arith_rule = "simp_arith"
val veriT_tmp_ite_elim_rule = "tmp_ite_elim"
val veriT_tmp_skolemize_rule = "tmp_skolemize"
val z3_skolemize_rule = Z3_Proof.string_of_rule Z3_Proof.Skolemize
val z3_th_lemma_rule_prefix = Z3_Proof.string_of_rule (Z3_Proof.Th_Lemma "")
val zipperposition_cnf_rule = "cnf"
(*Metitarski methods handled separately*)
val metitarski_decision_rule = "decision"
val metitarski_resolution_rule = "resolve"
val metitarski_canonicalize_rule = "canonicalize"
val metitarski_arithmetic_rule = "arithmetic"
val metitarski_conjunct_rule = "conjunct"
val metitarski_subst_rule = "subst"

val skolemize_rules =
  [e_definition_rule, e_skolemize_rule, leo2_extcnf_forall_neg_rule, satallax_skolemize_rule,
   spass_skolemize_rule, vampire_skolemisation_rule, veriT_tmp_ite_elim_rule,
   veriT_tmp_skolemize_rule, waldmeister_skolemize_rule, z3_skolemize_rule, zipperposition_cnf_rule]

fun is_ext_rule rule = (rule = leo2_extcnf_equal_neg_rule)
val is_maybe_ext_rule = is_ext_rule orf String.isPrefix satallax_tab_rule_prefix

val is_skolemize_rule = member (op =) skolemize_rules
fun is_arith_rule rule =
  String.isPrefix z3_th_lemma_rule_prefix rule orelse rule = veriT_simp_arith_rule orelse
  rule = veriT_la_generic_rule
val is_datatype_rule = String.isPrefix pirate_datatype_rule

fun is_metitarski_decision_rule rule = (rule = metitarski_decision_rule)
fun is_metitarski_resolution_rule rule = (rule = metitarski_resolution_rule)
fun is_metitarski_canonicalize_rule rule = (rule = metitarski_canonicalize_rule)
fun is_metitarski_arithmetic_rule rule = (rule = metitarski_arithmetic_rule)
fun is_metitarski_conjunct_rule rule = (rule = metitarski_conjunct_rule)
fun is_metitarski_subst_rule rule = (rule = metitarski_subst_rule)

fun raw_label_of_num num = (num, 0)

fun label_of_clause [(num, _)] = raw_label_of_num num
  | label_of_clause c = (space_implode "___" (map (fst o raw_label_of_num o fst) c), 0)

fun add_global_fact ss = apsnd (union (op =) ss)

(* A list with the names of all the metitarski axioms. Without the Bessel function.
  These are encoded in Isabelle as separate lemmas.
  The list is needed to make sure these facts are not removed from the "using" clauses because 
  they don't appear anywhere else in the proof. Should find a better way to do this.*)
val metitarski_axioms : string list =
  ["abs_negative", "abs_nonnegative",
   "abs_cases", "abs_pos", "abs_neg",
   "arccos_upper_bound", "arccos_lower_bound",
   "arcsin_lower_bound_pos_1", "arcsin_lower_bound_pos_2", "arcsin_lower_bound_pos_3", "arcsin_lower_bound_pos_5", "arcsin_lower_bound_neg_1", "arcsin_lower_bound_neg_2",
   "arcsin_upper_bound_pos_1", "arcsin_upper_bound_pos_2", "arcsin_upper_bound_neg_1", "arcsin_upper_bound_neg_2", "arcsin_upper_bound_neg_3", "arcsin_upper_bound_neg_5",
   "atan_upper_bound_case_41", "atan_upper_bound_case_42", "atan_upper_bound_case_43", "atan_upper_bound_case_44", "atan_lower_bound_case_41", "atan_lower_bound_case_42", "atan_lower_bound_case_43", "atan_lower_bound_case_44",
   "atan_upper_bound_case_51", "atan_upper_bound_case_52", "atan_upper_bound_case_53", "atan_upper_bound_case_54", "atan_lower_bound_case_51", "atan_lower_bound_case_52", "atan_lower_bound_case_53", "atan_lower_bound_case_54", "atan_upper_bound_case_63", "atan_lower_bound_case_63", 
   "atan_lower_bound_case_11", "atan_lower_bound_case_12", "atan_lower_bound_case_13", "atan_lower_bound_case_14", "atan_lower_bound_case_31", "atan_lower_bound_case_32", "atan_lower_bound_case_33", "atan_lower_bound_case_34",
   "atan_upper_bound_case_11", "atan_upper_bound_case_12", "atan_upper_bound_case_13", "atan_upper_bound_case_14", "atan_upper_bound_case_31", "atan_upper_bound_case_32", "atan_upper_bound_case_33", "atan_upper_bound_case_34",
   "cbrt_lower_bound_1", "cbrt_lower_bound_2_small", "cbrt_lower_bound_2", "cbrt_lower_bound_2_large", "cbrt_lower_bound_3",
   "cbrt_upper_bound_1", "cbrt_upper_bound_2_small", "cbrt_upper_bound_2", "cbrt_upper_bound_2_large", "cbrt_upper_bound_3",
   "cos_upper_bound_0", "cos_upper_bound_2", "cos_lower_bound_0", "cos_lower_bound_2",
   "cos_upper_bound_const_1", "cos_lower_bound_const_m1",
   "cos_upper_bound_1", "cos_upper_bound_3", "cos_upper_bound_5", "cos_lower_bound_1", "cos_lower_bound_3", "cos_lower_bound_5",
   "cos_upper_bound_7", "cos_lower_bound_7",
   "cosh_taylor_lower_bound_pos1", "cosh_taylor_lower_bound_neg1", "cosh_lower_bound_neg1", "cosh_lower_bound_pos1", "cosh_lower_bound_neg2", "cosh_lower_bound_pos2",
   "cosh_upper_bound_neg0", "cosh_upper_bound_pos1", "cosh_upper_bound_neg1", "cosh_upper_bound_pos2", "cosh_upper_bound_neg2",
   "cos_lower_bound_linear", "cos_upper_bound_linear", "exp_lower_bound_cf4", "exp_lower_bound_cf5", "exp_lower_bound_cf6", "exp_lower_bound_cf7", "exp_upper_bound_cf4", "exp_upper_bound_cf5", "exp_upper_bound_cf6", "exp_upper_bound_cf7",
   "exp_monotone1", "exp_monotone2", "exp_positive", "exp_lower_taylor_1", "exp_lower_taylor_5_cubed", "exp_lower_bound_cf2", "exp_lower_bound_cf3",
   "exp_upper_bound_case_3", "exp_upper_bound_case_5", "exp_upper_bound_cf1", "exp_upper_bound_cf2", "exp_upper_bound_cf3",
   "lgen_le_pos", "lgen_less_pos", "lgen_le_neg", "lgen_less_neg", "leq_left_divide_mul_pos", "leq_left_mul_divide_pos", "leq_right_divide_mul_pos", "leq_right_mul_divide_pos", "leq_left_divide_mul_neg", "leq_left_mul_divide_neg", "leq_right_divide_mul_neg", "leq_right_mul_divide_neg", "interval_intro", "interval_elim1", "interval_elim2",
   "ln_upper_bound_cf11", "ln_upper_bound_cf13", "ln_upper_bound_cf15", "ln_lower_bound_cf11", "ln_lower_bound_cf13", "ln_lower_bound_cf15",
   "ln_zero1", "ln_zero2", "ln_monotone1", "ln_monotone2", 
   "ln_lower_bound_cf1", "ln_lower_bound_cf3", "ln_lower_bound_cf5", "ln_lower_bound_cf7", "ln_lower_bound_cf9",
   "ln_upper_bound_cf1", "ln_upper_bound_cf3", "ln_upper_bound_cf5", "ln_upper_bound_cf7", "ln_upper_bound_cf9",
   "log_def",
   "max_1", "max_2", "min_1", "min_2",
   "nthrt_lower_bound_1", "nthrt_lower_bound_2_small", "nthrt_lower_bound_2", "nthrt_lower_bound_2_large", "nthrt_lower_bound_3",
   "nthrt_upper_bound_1", "nthrt_upper_bound_2_small", "nthrt_upper_bound_2", "nthrt_upper_bound_2_large", "nthrt_lower_bound_3",
   "pi_upper_bound", "pi_lower_bound",
   "pow_upper_bound", "pow_lower_bound", "pow_def",
   "sin_upper_bound_0_neg", "sin_upper_bound_0_pos", "sin_upper_bound_2_neg", "sin_upper_bound_2_pos", "sin_lower_bound_0_neg", "sin_lower_bound_0_pos", "sin_lower_bound_2_neg", "sin_lower_bound_2_pos",
   "sin_upper_bound_const_1", "sin_lower_bound_const_m1",
   "sin_upper_bound_1_neg", "sin_upper_bound_1_pos", "sin_upper_bound_3_neg", "sin_upper_bound_3_pos", "sin_upper_bound_5_neg", "sin_upper_bound_5_pos", "sin_lower_bound_1_neg", "sin_lower_bound_1_pos", "sin_lower_bound_3_neg", "sin_lower_bound_3_pos", "sin_lower_bound_5_neg", "sin_lower_bound_5_pos",
   "sin_upper_bound_7_neg", "sin_upper_bound_7_pos", "sin_lower_bound_7_neg", "sin_lower_bound_7_pos",
   "sinh_taylor_lower_bound_pos1", "sinh_lower_bound_neg1", "sinh_lower_bound_pos1", "sinh_lower_bound_neg2", "sinh_lower_bound_pos2",
   "sinh_taylor_upper_bound_neg1", "sinh_upper_bound_pos1", "sinh_upper_bound_neg1", "sinh_upper_bound_pos2", "sinh_upper_bound_neg2",
   "sin_lower_bound_linear", "sin_upper_bound_linear", 
   "sqrt_upper_bound_1", "sqrt_upper_bound_4", "sqrt_lower_bound_1", "sqrt_lower_bound_4",
   "sqrt_ge", "sqrt_le", "sqrt_monotone1", "sqrt_monotone2",
   "sqrt_squared", "sqrt_lower_bound_id", "sqrt_lower_bound_0", "sqrt_lower_bound_2_small", "sqrt_lower_bound_2", "sqrt_lower_bound_2_large",
   "sqrt_squared", "sqrt_upper_bound_0", "sqrt_upper_bound_2_small", "sqrt_upper_bound_2", "sqrt_upper_bound_2_large",
   "tan_upper_bound", "tan_lower_bound", "tan_def",
   "tanh_lower_bound_neg0", "tanh_lower_bound_neg1", "tanh_lower_bound_pos1", "tanh_lower_bound_neg2", "tanh_lower_bound_pos2",
   "tanh_upper_bound_neg1", "tanh_upper_bound_pos0", "tanh_upper_bound_pos1", "tanh_upper_bound_neg2", "tanh_upper_bound_pos2",
   "tan_lower_bound_pos0", "tan_lower_bound_pos1", "tan_lower_bound_pos2", "tan_lower_bound_neg1", "tan_lower_bound_neg2", "tan_lower_bound_neg3",
   "tan_upper_bound_pos1", "tan_upper_bound_pos2", "tan_upper_bound_pos3", "tan_upper_bound_neg0", "tan_upper_bound_neg1", "tan_upper_bound_neg2",
   "trans"
  ]

fun add_fact_of_dependency [(_, ss as _ :: _)] = add_global_fact ss
  | add_fact_of_dependency names = 
      (case names of
        [(n, [])] => if member (op =) metitarski_axioms n then add_global_fact [n]
                     else apfst (insert (op =) (label_of_clause names))
      | _ => apfst (insert (op =) (label_of_clause names))
      )
      

fun add_line_pass1 (line as (name, role, t, rule, [])) lines =
    (* No dependencies: lemma (for Z3), fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if role = Conjecture orelse role = Negated_Conjecture then
      line :: lines
    else if t aconv @{prop True} then
      map (replace_dependencies_in_line (name, [])) lines
    else if role = Lemma orelse role = Hypothesis orelse is_arith_rule rule then
      line :: lines
    else if role = Axiom then
      lines (* axioms (facts) need no proof lines *)
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line_pass1 line lines = line :: lines

fun add_lines_pass2 res [] = rev res
  | add_lines_pass2 res ((line as (name, role, t, rule, deps)) :: lines) =
    let
      fun normalize role =
        role = Conjecture ? (HOLogic.dest_Trueprop #> s_not #> HOLogic.mk_Trueprop)

      val norm_t = normalize role t
      val is_duplicate =
        exists (fn (prev_name, prev_role, prev_t, _, _) =>
            (prev_role = Hypothesis andalso prev_t aconv t) orelse
            (member (op =) deps prev_name andalso
             Term.aconv_untyped (normalize prev_role prev_t, norm_t)))
          res

      fun looks_boring () = t aconv @{prop False} orelse length deps < 2

      fun is_skolemizing_line (_, _, _, rule', deps') =
        is_skolemize_rule rule' andalso member (op =) deps' name

      fun is_before_skolemize_rule () = exists is_skolemizing_line lines
    in
      if is_duplicate orelse
          (role = Plain andalso not (is_skolemize_rule rule) andalso
           not (is_ext_rule rule) andalso not (is_arith_rule rule) andalso
           not (is_datatype_rule rule) andalso not (null lines) andalso looks_boring () andalso
           not (is_before_skolemize_rule ()) andalso
           (*We don't want to eliminate the MT "decision" and "arithmetic" steps 
             even if they have only one premise.
             Neither the "conjunct" step. Otherwise special function might be given to the 
             RCF procedure by mistake.
             "Subst" steps need to be handled separately in case they are instantiating 
             a MT free variable.*)
           not (is_metitarski_decision_rule rule) andalso  
           not (is_metitarski_arithmetic_rule rule) andalso
           not (is_metitarski_conjunct_rule rule) andalso 
           not (is_metitarski_subst_rule rule) )then
        add_lines_pass2 res (map (replace_dependencies_in_line (name, deps)) lines)
      else
        add_lines_pass2 (line :: res) lines
    end

type isar_params =
  bool * (string option * string option) * Time.time * real option * bool * bool
  * (term, string) atp_step list * thm

val basic_systematic_methods = [Metis_Method (NONE, NONE), Meson_Method, Blast_Method, SATx_Method]
val basic_simp_based_methods = [Auto_Method, Simp_Method, Fastforce_Method, Force_Method]
val basic_arith_methods = [Linarith_Method, Presburger_Method, Algebra_Method]

val arith_methods = basic_arith_methods @ basic_simp_based_methods @ basic_systematic_methods
val datatype_methods = [Simp_Method, Simp_Size_Method]
val systematic_methods =
  basic_systematic_methods @ basic_arith_methods @ basic_simp_based_methods @
  [Metis_Method (SOME full_typesN, NONE), Metis_Method (SOME no_typesN, NONE)]
val rewrite_methods = basic_simp_based_methods @ basic_systematic_methods @ basic_arith_methods
val skolem_methods = Moura_Method :: systematic_methods

(*For the metitarski decision steps*)
val metitarski_decision_methods = [Sos_Method]
(*We want to try both of these in case there's a substitution step hidden inside.
  Auto sometimes also works for tainted sequents that were inverted 
  (the ones that generate a case split)*)
val metitarski_resolution_methods = [Metis_Method (NONE, NONE)] @ basic_simp_based_methods @ [Blast_Method]
(*Handle the MT canonicalize steps separately*)
val metitarski_canonicalize_methods = [Auto_Method]
(*For MT arithmetic steps*)
val metitarski_arithmetic_methods = [MT_Arith_Method] (*[Sorry_Method]*) (*[Simp_Method, Auto_Method]*)
(*For subst steps*)
val metitarski_subst_methods = [Auto_Method, Blast_Method]

fun isar_proof_text ctxt debug num_chained isar_proofs smt_proofs isar_params
    (one_line_params as ((used_facts, (_, one_line_play)), banner, subgoal, subgoal_count)) =
  let
    val _ = if debug then writeln "Constructing Isar proof..." else ()

    fun generate_proof_text () =
      let
        val (verbose, alt_metis_args, preplay_timeout, compress, try0, minimize, atp_proof0, goal) =
          isar_params ()
      in
        if null atp_proof0 then
          one_line_proof_text ctxt 0 one_line_params
        else
          let
            val systematic_methods' = insert (op =) (Metis_Method alt_metis_args) systematic_methods

            fun massage_methods (meths as meth :: _) =
              if not try0 then [meth]
              else if smt_proofs = SOME true then SMT_Method :: meths
              else meths

            val (params, _, concl_t) = strip_subgoal goal subgoal ctxt
            val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) params
            val ctxt = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd

            val do_preplay = preplay_timeout <> Time.zeroTime
            val compress =
              (case compress of
                NONE => if isar_proofs = NONE andalso do_preplay then 1000.0 else 10.0
              | SOME n => n)

            fun is_fixed ctxt = Variable.is_declared ctxt orf Name.is_skolem
            fun skolems_of ctxt t = Term.add_frees t [] |> filter_out (is_fixed ctxt o fst) |> rev

            fun get_role keep_role ((num, _), role, t, rule, _) =
              if keep_role role then SOME ((raw_label_of_num num, t), rule) else NONE

            val atp_proof =
              fold_rev add_line_pass1 atp_proof0 []
              |> add_lines_pass2 []
           
            (*  val _ = @{print} atp_proof  *)
              
            val conjs =
              map_filter (fn (name, role, _, _, _) =>
                  if member (op =) [Conjecture, Negated_Conjecture] role then SOME name else NONE)
                atp_proof
            val assms = map_filter (Option.map fst o get_role (curry (op =) Hypothesis)) atp_proof

            fun add_lemma ((l, t), rule) ctxt =
              let
                val (skos, meths) =
                  (if is_skolemize_rule rule then (skolems_of ctxt t, skolem_methods)
                   else if is_arith_rule rule then ([], arith_methods)
                   else ([], rewrite_methods))
                  ||> massage_methods
              in
                (Prove ([], skos, l, t, [], ([], []), meths, ""),
                 ctxt |> not (null skos) ? (Variable.add_fixes (map fst skos) #> snd))
              end

            val (lems, _) =
              fold_map add_lemma (map_filter (get_role (curry (op =) Lemma)) atp_proof) ctxt

            val bot = #1 (List.last atp_proof)

            val refute_graph =
              atp_proof
              |> map (fn (name, _, _, _, from) => (from, name))
              |> make_refute_graph bot
              |> fold (Atom_Graph.default_node o rpair ()) conjs

            val axioms = axioms_of_refute_graph refute_graph conjs

            val tainted = tainted_atoms_of_refute_graph refute_graph conjs
            val is_clause_tainted = exists (member (op =) tainted)
            val steps =
              Symtab.empty
              |> fold (fn (name as (s, _), role, t, rule, _) =>
                  Symtab.update_new (s, (rule, t
                    |> (if is_clause_tainted [name] then
                          HOLogic.dest_Trueprop
                          #> role <> Conjecture ? s_not
                          #> fold exists_of (map Var (Term.add_vars t []))
                          #> HOLogic.mk_Trueprop
                        else
                          I))))
                atp_proof

            fun is_referenced_in_step _ (Let _) = false
              | is_referenced_in_step l (Prove (_, _, _, _, subs, (ls, _), _, _)) =
                member (op =) ls l orelse exists (is_referenced_in_proof l) subs
            and is_referenced_in_proof l (Proof (_, _, steps)) =
              exists (is_referenced_in_step l) steps

            fun insert_lemma_in_step lem
                (step as Prove (qs, fix, l, t, subs, (ls, gs), meths, comment)) =
              let val l' = the (label_of_isar_step lem) in
                if member (op =) ls l' then
                  [lem, step]
                else
                  let val refs = map (is_referenced_in_proof l') subs in
                    if length (filter I refs) = 1 then
                      let
                        val subs' = map2 (fn false => I | true => insert_lemma_in_proof lem) refs
                          subs
                      in
                        [Prove (qs, fix, l, t, subs', (ls, gs), meths, comment)]
                      end
                    else
                      [lem, step]
                  end
              end
            and insert_lemma_in_steps lem [] = [lem]
              | insert_lemma_in_steps lem (step :: steps) =
                if is_referenced_in_step (the (label_of_isar_step lem)) step then
                  insert_lemma_in_step lem step @ steps
                else
                  step :: insert_lemma_in_steps lem steps
            and insert_lemma_in_proof lem (Proof (fix, assms, steps)) =
              Proof (fix, assms, insert_lemma_in_steps lem steps)

            val rule_of_clause_id = fst o the o Symtab.lookup steps o fst

            val finish_off = close_form #> rename_bound_vars

            fun prop_of_clause [(num, _)] = Symtab.lookup steps num |> the |> snd |> finish_off
              | prop_of_clause names =
                let
                  val lits =
                    map (HOLogic.dest_Trueprop o snd) (map_filter (Symtab.lookup steps o fst) names)
                in
                  (case List.partition (can HOLogic.dest_not) lits of
                    (negs as _ :: _, pos as _ :: _) =>
                    s_imp (Library.foldr1 s_conj (map HOLogic.dest_not negs),
                      Library.foldr1 s_disj pos)
                  | _ => fold (curry s_disj) lits @{term False})
                end
                |> HOLogic.mk_Trueprop |> finish_off

            fun maybe_show outer c = if outer andalso eq_set (op =) (c, conjs) then [Show] else []

            fun is_show outer c : bool = outer andalso eq_set (op =) (c, conjs)
            val thesis_var = ((Auto_Bind.thesisN, 0), HOLogic.boolT)

            fun isar_steps outer predecessor accum [] =
                accum
                |> (if tainted = [] then
                      (* e.g., trivial, empty proof by Z3 *)
                      cons (Prove (if outer then [Show] else [], [], no_label, concl_t, [],
                        sort_facts (the_list predecessor, []), massage_methods systematic_methods',
                        ""))
                    else
                      I)
                |> rev
              | isar_steps outer _ accum (Have (id, (gamma, c)) :: infs) =
                let
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  (*val _ = @{print} t*)
                  val rule = rule_of_clause_id id
                  val skolem = is_skolemize_rule rule

                  val deps = ([], [])
                    |> fold add_fact_of_dependency gamma
                    |> is_maybe_ext_rule rule ? add_global_fact [short_thm_name ctxt ext]
                    (*If this is an arithmetic step, add algebra_simps to the simplifier. Not using this anymore*)
                    (*|> is_metitarski_arithmetic_rule rule ? add_global_fact ["metitarski_simps algebra_simps"]*)
                    |> sort_facts

                  val meths =
                     (*If we are dealing with a resolution step, we don't want to only try metis
                       but also auto, because there might be substitution steps hidden inside. 
                       If try0 is false, massage_methods only return the first method 
                       from the method list given to it.
                       Auto sometimes also works for tainted sequents that were inverted 
                       (the ones that generate a case split)*)
                     if (not try0) andalso (is_metitarski_resolution_rule rule)
                       then metitarski_resolution_methods
                     (*If this is a metitarski skolemize step then try all known skolemization rules,
                       not just the first one. Because moura doesn't work well for MT skolemization.*)
                     else if (not try0) andalso skolem andalso String.isSubstring "metitarski" banner
                       then skolem_methods
                     (*Handle metitarski arithmetic steps separately*)
                     else if is_metitarski_arithmetic_rule rule then metitarski_arithmetic_methods
                     (*For subst steps*)
                     else if is_metitarski_subst_rule rule then metitarski_subst_methods
                     else  
                       ((if skolem then skolem_methods
                       else if is_arith_rule rule then arith_methods
                       else if is_datatype_rule rule then datatype_methods
                       (*Special rules for metitarski decision steps*)
                       else if is_metitarski_decision_rule rule then metitarski_decision_methods
                       (*Handle canonicalize steps separately*)
                       else if is_metitarski_canonicalize_rule rule then metitarski_canonicalize_methods                       
                       else systematic_methods')
                      |> massage_methods)

                  fun prove sub facts =
                    (*When reconstructing a metitarski proof, always use ?thesis in the "show" step*)
                    Prove (maybe_show outer c, [], l, 
                      if String.isSubstring "metitarski" banner andalso is_show outer c
                        then HOLogic.mk_Trueprop (Var thesis_var)
                        else t, 
                      sub, facts, meths, "")
                  fun steps_of_rest step = isar_steps outer (SOME l) (step :: accum) infs
                in
                  if is_clause_tainted c then
                    (case gamma of
                      [g] =>
                      if skolem andalso is_clause_tainted g then
                        let
                          val skos = skolems_of ctxt (prop_of_clause g)
                          val subproof = Proof (skos, [], rev accum)
                        in
                          isar_steps outer (SOME l) [prove [subproof] ([], [])] infs
                        end
                      else
                        steps_of_rest (prove [] deps)
                    | _ => steps_of_rest (prove [] deps))
                  else
                    steps_of_rest
                      (if skolem then
                         (case skolems_of ctxt t of
                           [] => prove [] deps
                         | skos => Prove ([], skos, l, t, [], deps, meths, ""))
                       else
                         prove [] deps)
                end
              | isar_steps outer predecessor accum (Cases cases :: infs) =
                let
                  fun isar_case (c, subinfs) =
                    isar_proof false [] [(label_of_clause c, prop_of_clause c)] [] subinfs
                  val c = succedent_of_cases cases
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val step =
                    (*When reconstructing a metitarski proof, always use ?thesis in the "show" step*)
                    Prove (maybe_show outer c, [], l, 
                      if String.isSubstring "metitarski" banner andalso is_show outer c
                        then HOLogic.mk_Trueprop (Var thesis_var)
                        else t,
                      map isar_case (filter_out (null o snd) cases),
                      sort_facts (the_list predecessor, []), massage_methods systematic_methods',
                      "")
                in
                  isar_steps outer (SOME l) (step :: accum) infs
                end
            and isar_proof outer fix assms lems infs =
              Proof (fix, assms,
                fold_rev insert_lemma_in_steps lems (isar_steps outer NONE [] infs))

            val trace = Config.get ctxt trace

            val canonical_isar_proof =
              refute_graph
              |> trace ? tap (tracing o prefix "Refute graph:\n" o string_of_refute_graph)
              |> redirect_graph axioms tainted bot
              |> trace ? tap (tracing o prefix "Direct proof:\n" o string_of_direct_proof)
              |> isar_proof true params assms lems
              |> postprocess_isar_proof_remove_show_stuttering
              |> postprocess_isar_proof_remove_unreferenced_steps I
              |> relabel_isar_proof_canonically

            val ctxt = ctxt |> enrich_context_with_local_facts canonical_isar_proof

            val preplay_data = Unsynchronized.ref Canonical_Label_Tab.empty

            val _ = fold_isar_steps (fn meth =>
                K (set_preplay_outcomes_of_isar_step ctxt preplay_timeout preplay_data meth []))
              (steps_of_isar_proof canonical_isar_proof) ()

            fun str_of_preplay_outcome outcome =
              if Lazy.is_finished outcome then string_of_play_outcome (Lazy.force outcome) else "?"
            fun str_of_meth l meth =
              string_of_proof_method ctxt [] meth ^ " " ^
              str_of_preplay_outcome
                (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth)
            fun comment_of l = map (str_of_meth l) #> commas

            fun trace_isar_proof label proof =
              if trace then
                tracing (timestamp () ^ "\n" ^ label ^ ":\n\n" ^
                  string_of_isar_proof ctxt subgoal subgoal_count
                    (comment_isar_proof comment_of proof) ^ "\n")
              else
                ()

            fun comment_of l (meth :: _) =
              (case (verbose,
                  Lazy.force (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth)) of
                (false, Played _) => ""
              | (_, outcome) => string_of_play_outcome outcome)

            val (play_outcome, isar_proof) =
              canonical_isar_proof
              |> tap (trace_isar_proof "Original")
              |> compress_isar_proof ctxt compress preplay_timeout preplay_data
              |> tap (trace_isar_proof "Compressed")
              |> postprocess_isar_proof_remove_unreferenced_steps
                   (keep_fastest_method_of_isar_step (!preplay_data)
                    #> minimize ? minimize_isar_step_dependencies ctxt preplay_data)
              |> tap (trace_isar_proof "Minimized")
              |> `(preplay_outcome_of_isar_proof (!preplay_data))
              ||> (comment_isar_proof comment_of
                   #> chain_isar_proof
                   #> kill_useless_labels_in_isar_proof
                   #> relabel_isar_proof_nicely
                   #> rationalize_obtains_in_isar_proofs ctxt)
          in
            (case (num_chained, add_isar_steps (steps_of_isar_proof isar_proof) 0) of
              (0, 1) =>
              one_line_proof_text ctxt 0
                (if play_outcome_ord (play_outcome, one_line_play) = LESS then
                   (case isar_proof of
                     Proof (_, _, [Prove (_, _, _, _, _, (_, gfs), meth :: _, _)]) =>
                     let
                       val used_facts' = filter (fn (s, (sc, _)) =>
                         member (op =) gfs s andalso sc <> Chained) used_facts
                     in
                       ((used_facts', (meth, play_outcome)), banner, subgoal, subgoal_count)
                     end)
                 else
                   one_line_params) ^
              (if isar_proofs = SOME true then "\n(No Isar proof available.)" else "")
            | (_, num_steps) =>
              let
                val msg =
                  (if verbose then [string_of_int num_steps ^ " step" ^ plural_s num_steps]
                   else []) @
                  (if do_preplay then [string_of_play_outcome play_outcome] else [])
              in
                one_line_proof_text ctxt 0 one_line_params ^
                "\n\nIsar proof" ^ (commas msg |> not (null msg) ? enclose " (" ")") ^ ":\n" ^
                Active.sendback_markup_command
                  (string_of_isar_proof ctxt subgoal subgoal_count isar_proof)
              end)
          end
      end
  in
    if debug then
      generate_proof_text ()
    else
      (case try generate_proof_text () of
        SOME s => s
      | NONE =>
        one_line_proof_text ctxt 0 one_line_params ^
        (if isar_proofs = SOME true then "\nWarning: Isar proof construction failed" else ""))
  end

fun isar_proof_would_be_a_good_idea smt_proofs (meth, play) =
  (case play of
    Played _ => meth = SMT_Method andalso smt_proofs <> SOME true
  | Play_Timed_Out time => time > Time.zeroTime
  | Play_Failed => true)

fun proof_text ctxt debug isar_proofs smt_proofs isar_params num_chained
    (one_line_params as ((_, preplay), _, _, _)) =
  (if isar_proofs = SOME true orelse
      (isar_proofs = NONE andalso isar_proof_would_be_a_good_idea smt_proofs preplay) then
     isar_proof_text ctxt debug num_chained isar_proofs smt_proofs isar_params
   else
     one_line_proof_text ctxt num_chained) one_line_params

end;
