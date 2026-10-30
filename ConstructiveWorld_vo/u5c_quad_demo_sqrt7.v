(* Five-field header
   1. Mission: non-invasive sqrt-7 demonstration piece for the uniform
      escape parameterization (GEDAN-sqrt-d P2).  The P1 artifact
      u5c_quad_uniform_escape (KB58 born, four-gate green) proves the
      uniform statement quadratic_uniform_escape : forall (d : positive)
      (Hd : u5c_quad_nonsq d) (q : Q), sigT (fun c : Q => And (QltT 0 c)
      (real_lt (real_const c) (real_metric <Newton seq of sqrt d>
      (real_const q)))), with the non-square premise carried at Set level
      by u5c_quad_nonsq d := Id (Z.eqb (Z.sqrt d * Z.sqrt d) d) false.
      This demo instantiates the whole family at d = 7 by ONE explicit
      instantiation call.  The only new mathematical content is the explicit Set-level
      non-square carrier u5c_nonsq7 (Z.sqrt 7 = 2, 2*2 = 4 <> 7); the
      escape statement itself is consumed read-only from P1.  Contrast:
      the pool artifact u5c_inst_sqrt5.v reached the same shape for d = 5
      through a full hand-copied adaptation (is5_x / is5_delta / is5_e /
      is5_tail / is5_vanish / is5_escape, 1300+ lines, admitted by its own
      header to be a line-by-line isomorphic clone of u5c_inst_sqrt3);
      the parameterized P1 face reduces a new d to a witness plus a
      one-line application, which is exactly the parameterization dividend
      demonstrated here.
   2. Dependencies: u5c_quad_uniform_escape (P1, require-only, zero
      modification), S01_BaseRing (Set-level Id / id_refl),
      S02_CauchyComplete (QltT / QleT' / Qseq / cauchy / real_lt /
      real_const), S03_QExp (real_metric), UpReqIrrationalCriterion
      (lic_seq_cauchy); Stdlib QArith, ZArith, Arith, Bool, Extraction.
      All consumed files are require-only; this piece adds no axioms and
      no classical logic.
   3. Benchmark lines: u5c_quad_uniform_escape.v quadratic_uniform_escape
      (consumed mother theorem, one-argument instantiation at d = 7);
      u5c_inst_sqrt5.v u5c_sqrt5_criterion_escape_pt (manual
      copy-adaptation contrast, NOT consumed); u5c_quad_margin_closed
      (P1 four-branch margin core) consumed at the feasible window index
      n0 = 3 for the certified numeric table.
   4. Constructivity: the statement face is entirely Set-carried
      (Id / sigT / And / QltT / QleT'), zero new Prop axioms.  u5c_nonsq7
      : u5c_quad_nonsq 7 is closed by id_refl up to conversion
      (Z.eqb (Z.sqrt 7 * Z.sqrt 7) 7 computes to false); u5c_demo7_escape
      is a plain Definition by application of the P1 theorem - no proof,
      no new lemmas.  Sample certificates u5c_demo7_q3_cert /
      u5c_demo7_q2_cert consume u5c_quad_margin_closed at n0 = 3 with the
      e-bound premise discharged by pure conversion (Qle_bool computes);
      branch tags and margin booleans are conversion-closed Id-true facts
      over Qlt_bool / Qle_bool (vm_compute face).  Prop appears only in
      the proof-internal premise (1 <= 3)%nat of margin_closed, per the
      pool convention.  Certified numeric table (exact rationals):
        K_7 = 4*7 + 8 = 36, c = 1/36, x_7(3) = 977/368,
        e_7(3) = 6561/270848, margin = 1/18 + e_7(3) = 388946/4875264
        = 0.0797...;
        q = 3 (branch 3: q^2 = 9 > 7 and q <= (d+1)/2 = 4):
          margin 0.0797... < |x_7(3) - 3| = 127/368 = 0.3451...
          (true |sqrt 7 - 3| = 0.3542...);
        q = 2 (branch 2: 0 < q and q^2 = 4 < 7):
          margin 0.0797... < |x_7(3) - 2| = 241/368 = 0.6548...
          (true |sqrt 7 - 2| = 0.6457...).
   5. Build:
      C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe -native-compiler no -q
        -Q D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo ""
        -Q D:/ComplexAnalysis/attn/kb58_work_20261029 ""
        u5c_quad_demo_sqrt7.v
      (run from D:/ComplexAnalysis/attn/kb63_work_20261029, wrapped in
      _guard_v3.ps1 with TempLimit 98, per the thermal-control rule). *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqIrrationalCriterion.
Require Import u5c_quad_uniform_escape.
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith
  Arith.Arith Bool.Bool.

(* S1. Explicit Set-level non-square carrier for d = 7.
   u5c_quad_nonsq 7 unfolds to Id (Z.eqb (Z.sqrt 7 * Z.sqrt 7) 7) false;
   Z.sqrt 7 computes to 2 and Z.eqb 4 7 computes to false, so the plain
   constructor closes the definition up to conversion (vm_compute face). *)
Definition u5c_nonsq7 : u5c_quad_nonsq 7%positive := id_refl.

(* S2. The one-argument call: the first quadratic instance obtained by
   plain application of the P1 artifact.  No sequence, no decay lemma, no window:
   the entire escape statement for sqrt 7 is inherited from P1. *)
Definition u5c_demo7_escape : forall q : Q,
  sigT (fun c : Q => And (QltT 0 c)
    (real_lt (real_const c)
       (real_metric (existT (fun u : Qseq => cauchy u)
          (u5c_quad_x 7%positive)
          (lic_seq_cauchy (u5c_quad_x 7%positive) (u5c_quad_e 7%positive)
             (u5c_quad_tail 7%positive u5c_nonsq7)
             (u5c_quad_vanish 7%positive u5c_nonsq7)))
          (real_const q))))
  := quadratic_uniform_escape 7%positive u5c_nonsq7.

(* S3. Certified numeric table at the feasible window index n0 = 3.
   P1's uniform window index for d = 7, b = 1 is n0 = 2*7 + 2*1 + K_7 = 52
   (infeasible for exact rational evaluation); its margin core
   u5c_quad_margin_closed holds at every n0 >= 1 once the e-bound premise
   QleT' (e 7 n0) (1/(K_7 b^2)) is supplied.  At n0 = 3 the e-bound holds
   by pure conversion: e_7(3) = 6561/270848 <= 1/36 since
   6561 * 36 = 236196 <= 270848. *)

Definition u5c_demo7_b1 : positive := 1%positive.

(* e-bound premise at the sample index, discharged by conversion. *)
Definition u5c_demo7_e3_cbound :
  QleT' (u5c_quad_e 7%positive 3)
        ((1 # (u5c_quad_K 7%positive * (u5c_demo7_b1 * u5c_demo7_b1)))%Q)
  := id_refl.

(* The margin core's nat premise (proof-internal, pool convention). *)
Lemma u5c_demo7_n03 : (1 <= 3)%nat.
Proof. repeat constructor. Qed.

(* Sample point q = 3 = 3/1 (branch 3): certified margin 2c + e_7(3)
   bounded by |x_7(3) - 3|. *)
Definition u5c_demo7_q3_cert :
  QleT' (((1 # (u5c_quad_K 7%positive * (u5c_demo7_b1 * u5c_demo7_b1)))%Q
          + (1 # (u5c_quad_K 7%positive * (u5c_demo7_b1 * u5c_demo7_b1)))%Q
          + u5c_quad_e 7%positive 3)%Q)
        (Qabs (((3 # 1)%Q - u5c_quad_x 7%positive 3)%Q))
  := u5c_quad_margin_closed 7%positive u5c_nonsq7 3%Z u5c_demo7_b1 3
       u5c_demo7_n03 u5c_demo7_e3_cbound.

(* Sample point q = 2 = 2/1 (branch 2): same margin bounded by
   |x_7(3) - 2|. *)
Definition u5c_demo7_q2_cert :
  QleT' (((1 # (u5c_quad_K 7%positive * (u5c_demo7_b1 * u5c_demo7_b1)))%Q
          + (1 # (u5c_quad_K 7%positive * (u5c_demo7_b1 * u5c_demo7_b1)))%Q
          + u5c_quad_e 7%positive 3)%Q)
        (Qabs (((2 # 1)%Q - u5c_quad_x 7%positive 3)%Q))
  := u5c_quad_margin_closed 7%positive u5c_nonsq7 2%Z u5c_demo7_b1 3
       u5c_demo7_n03 u5c_demo7_e3_cbound.

(* S4. Raw numeric samples (vm_compute face; every body is id_refl up to
   conversion of Qlt_bool / Qle_bool / Q arithmetic on exact rationals). *)

(* Sequence value and error value at the sample index. *)
Lemma u5c_demo7_x3_value : u5c_quad_x 7%positive 3 == (977 # 368)%Q.
Proof. reflexivity. Qed.

Lemma u5c_demo7_e3_value : u5c_quad_e 7%positive 3 == (6561 # 270848)%Q.
Proof. reflexivity. Qed.

(* q = 3: certified margin 1/18 + e_7(3) = 388946/4875264 is strictly
   below |x_7(3) - 3| = 127/368. *)
Definition u5c_demo7_q3_margin :
  QltT ((1 # 18)%Q + u5c_quad_e 7%positive 3)%Q
       (Qabs (((3 # 1)%Q - u5c_quad_x 7%positive 3)%Q))
  := id_refl.

(* q = 2: same certified margin strictly below |x_7(3) - 2| = 241/368. *)
Definition u5c_demo7_q2_margin :
  QltT ((1 # 18)%Q + u5c_quad_e 7%positive 3)%Q
       (Qabs (((2 # 1)%Q - u5c_quad_x 7%positive 3)%Q))
  := id_refl.

(* Branch tags.  q = 3 sits in branch 3 (q^2 = 9 > 7 and q <= (7+1)/2). *)
Definition u5c_demo7_q3_branch3 :
  Id (andb (Qlt_bool (7 # 1)%Q (((3 # 1)%Q * (3 # 1)%Q)%Q))
           (Qle_bool ((3 # 1)%Q) (((7 + 1) # 2)%Q))) true
  := id_refl.

(* q = 2 sits in branch 2 (0 < q and q^2 = 4 < 7). *)
Definition u5c_demo7_q2_branch2 :
  Id (andb (Qlt_bool 0%Q (2 # 1)%Q)
           (Qlt_bool (((2 # 1)%Q * (2 # 1)%Q)%Q) (7 # 1)%Q)) true
  := id_refl.

(* G3 face: separate extraction of the demo constants (double-sided
   Obj.magic audit runs on the .ml / .mli pair). *)
From Stdlib Require Import Extraction.
Separate Extraction u5c_demo7_escape u5c_nonsq7 u5c_demo7_q3_cert
  u5c_demo7_q2_cert u5c_demo7_q3_margin u5c_demo7_q2_margin
  u5c_demo7_q3_branch3 u5c_demo7_q2_branch2.

(* G4 face: assumption audit. *)
Print Assumptions u5c_demo7_escape.
Print Assumptions u5c_demo7_q3_cert.
