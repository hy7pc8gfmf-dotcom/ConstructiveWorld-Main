(* ============================================================ *)
(* abl_loeb_d3_spec.v — Löb D3 使用面：ν₂ 谱带分类器 × Box2 凭证层                     *)
(*   → Goodstein 谱面使用定理（lbc_ 前缀；使用 G10_LoebFam 与 abl_loeb_d3 /             *)
(*   _ext / _prf2 / _prf2b / _nofix 五件遗产，把 σ₈ 分离子与有界可证性                    *)
(*   升格为逐档可判的独立带定理）                                                    *)
(*                                                                *)
(* 使命: 让「有界可证谓词无对角不动点」从存在性成果升格为可计算应用的成果：                  *)
(*   ① σ₈ 分离子对具体谓词族的有效应用形（可计算盲性凭证）；                               *)
(*   ② Box2 凭证层上的谱桥：ν₂ 值域四档 × 两盒肯定域的逐档完全分类；                        *)
(*   ③ Goodstein 谱面使用定理：机器层（dPrf2 重演）× 分离层（σ₈）                          *)
(*     合成的「单凭证双盒分离」显式定理形态。                                            *)
(*                                                                *)
(* 【主定理（中英双语，落笔前自审）】                                                *)
(*                                                                *)
(* 中文：在 pairp 2-adic 分离编码的账本可证性代数中：                                  *)
(*   (C1)【谱带分类器】lbc_band_class : nat → band 按 ν₂ 把每个码分档为四带之一               *)
(*         （0–3 项带／4–5 旧公式带／6–8 证明带／≥9 新层带），五层码族的档位逐构造子              *)
(*         可读：⌜t⌝ 在低带、⌜g⌝ 在旧带、⌜f⌝₂ 与 gnPrf2 凭证码在高带；MP2 合成码 MPc2             *)
(*         与界闭包 lbg_boxup2 恒在高带——合成子的档位由构造子决定，与运算对象无关                  *)
(*         （遗传分层读出的可计算形态）。                                              *)
(*   (C2)【盒的档位可靠性】旧盒 lbd_Box 肯定码 c 则 c 必在旧带（ν₂ ∈ {4,5}）；                  *)
(*         新盒 lbg_Box2 肯定 c 则 c 必在高带（ν₂ ∈ {9,10,11}）。                            *)
(*   (C3)【全谱盲性分类】对一切界与码，两盒的盲性由分类器逐档完全决定——                        *)
(*         低带与证明带对两盒皆盲；旧带仅旧盒可及；高带仅新盒可及。                            *)
(*   (C4)【独立带的 sigT 见证】存在带 k：旧盒独立带谓词在 k 取真，且一切对角候选                  *)
(*         ⌜diag th⌝₂ 的档位皆为 k——对角族整体居住在旧盒的独立带内；两非独立带                  *)
(*         各有显式 sigT 可肯定见证（界与码皆闭式给出）。                                     *)
(*   (C5)【σ₈ 有效应用形】对任意 F2 参量化码族 F，凭证 σ₈∘F 是旧盒盲性的可计算判据：            *)
(*         假侧 ⟹ 该族码在一切界下恒盲；对角候选族上该凭证恒取假——                            *)
(*         「对角不动点肯定不存在」逐族逐码有总可计算凭证。                                    *)
(*   (C6)【Goodstein 谱面使用主定理】单凭证双盒分离：任一 Prf2 凭证 pf 同时给出                   *)
(*         (i) 凭证码与目标码的档位（皆高带）、(ii) 新盒在闭式界 S(凭证码) 处的肯定、              *)
(*         (iii) 旧盒在一切界下的盲、(iv) σ₈ 分离值假；谱面无不动点定理把任意                      *)
(*         F2 句的档位 k 钉死为高带，并连带 σ₈ 假、旧盒盲、Löb 固定式空洞恒真。                  *)
(*                                                                *)
(* English: In the ledger provability algebra with pairp 2-adic separation               *)
(*   encoding: (C1) the band classifier lbc_band_class assigns to every code             *)
(*   one of four bands by its 2-adic valuation (0–3 terms, 4–5 old formulas,             *)
(*   6–8 proofs, ≥9 new layer); the band of each code family is readable                *)
(*   constructor-wise, and MP2-synthesized codes and bound closures live in              *)
(*   the high band regardless of their operands — the computable form of a               *)
(*   hereditary layer readout. (C2) Band soundness: an old-box affirmation               *)
(*   places the code in the old band; a new-box affirmation places it in the             *)
(*   high band. (C3) Spectral blindness classification: for every bound and              *)
(*   code, the blindness of both boxes is completely determined band-wise by             *)
(*   the classifier (a dependent-match theorem). (C4) The independence band              *)
(*   carries a sigT witness: some band k makes the old-box independence                 *)
(*   predicate true, and every diagonal candidate lands in k; each                       *)
(*   non-independent band carries an explicit affirmability witness with                *)
(*   closed code and bound. (C5) Effective form of the separator: for any               *)
(*   F2-parametrized code family F, the certificate σ₈∘F is a computable                *)
(*   blindness judge (false side implies blindness at every bound), and it              *)
(*   constantly returns false on the diagonal family. (C6) Flagship: every              *)
(*   Prf2 certificate simultaneously certifies (i) the band of its own and of            *)
(*   the target code, (ii) new-box affirmation at the closed bound S(certificate          *)
(*   code), (iii) old-box blindness at every bound, (iv) the false σ₈ value;             *)
(*   the spectral no-fixed-point theorem pins the band of any F2 sentence to            *)
(*   the high band, with σ₈ false, old-box blindness, and the vacuously true              *)
(*   Löbian fixed form delivered alongside.                                             *)
(*                                                                *)
(* 构造性: 纯构造性零承认——本件零 Section 变量、零假设声明、零公理：语句皆无条件全称形          *)
(*   或闭展品；分类器的四档划分在语句面就地消解（依赖 match 定理逐档交付）；文末                    *)
(*   Print Assumptions 全部 Closed under the global context。                              *)
(*                                                                *)
(* 依赖: Require Import G10_LoebFam + abl_loeb_d3 + abl_loeb_d3_ext +                    *)
(*   abl_loeb_d3_prf2 + abl_loeb_d3_prf2b + abl_loeb_d3_nofix。先按依赖序编上游五件               *)
(*   （池内 byte 级拷贝，md5 与源件一致），再编本件：                                      *)
(*   编译配方: rocq c -native-compiler no -q -Q <池> "" -Q <vo_local 树> "" <件>.v           *)
(*   （Rocq 9.1.0，live switch；G10_LoebFam 从缓存 .vo 解析，池内不留其拷贝。）                 *)
(*                                                                *)
(* 【诚实边界（fail-loud）】                                                            *)
(*   1. 「独立带」是「旧盒恒盲」的 Set 面重述，不是 Gödel 语义独立性；Goodstein 类比是               *)
(*      结构性的（2-adic 赋值读取＝遗传层级分档的直接读出），本件不断言任何 PA 不可证性。          *)
(*   2. σ₈ 凭证是单侧判据：假侧 ⟹ 一切界无条件盲；真侧仅给出必要性（该档肯定不被分离子               *)
(*      排除），逐码肯定存在性仍受有界搜索墙（rLPO 谱系）约束——墙原样保留，未触碰。               *)
(*   3. 新盒在其自身高带内可肯定（有 Prf2 凭证即点火，HBL1）；本件交付的是两盒可肯定                 *)
(*      档位的不相交（旧带 vs 高带），非「新盒亦无不动点」。                                    *)
(*   4. 分类定理的否定面（独立带恒盲）与肯定面（非独立带的显式可肯定见证）成对交付：               *)
(*      低带与证明带对两盒皆盲（分类定理覆盖），旧带与高带各有闭式见证——四档无一悬置。              *)
(* ============================================================ *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.
Require Import abl_loeb_d3_ext.
Require Import abl_loeb_d3_prf2.
Require Import abl_loeb_d3_prf2b.
Require Import abl_loeb_d3_nofix.

(* ===================================================================== *)
(* §A  谱带类型与分类器：ν₂ 值域的四档划分（编码即赋值，赋值即档位）                              *)
(* ===================================================================== *)

(* 四档谱带：低带 0–3（项码）、旧带 4–5（Formula 码，旧盒可见带）、
   证明带 6–8（D1 凭证码）、高带 ≥9（Formula2 码与 Prf2 凭证码）。 *)
Inductive lbc_band : Set :=
| lbc_band_low : lbc_band
| lbc_band_old : lbc_band
| lbc_band_mid : lbc_band
| lbc_band_high : lbc_band.

(* 谱带分类器：按 ν₂ 读档——继承 lbh_nu2 的燃料递归与可计算性，
   9 为新旧世界的分水岭（σ₈ 的阈值）。 *)
Definition lbc_band_class (c : nat) : lbc_band :=
  match lbh_nu2 c with
  | O => lbc_band_low
  | Datatypes.S O => lbc_band_low
  | Datatypes.S (Datatypes.S O) => lbc_band_low
  | Datatypes.S (Datatypes.S (Datatypes.S O)) => lbc_band_low
  | Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))) => lbc_band_old
  | Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O)))) => lbc_band_old
  | Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S O))))) =>
      lbc_band_mid
  | Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
          (Datatypes.S O)))))) => lbc_band_mid
  | Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
          (Datatypes.S (Datatypes.S O))))))) => lbc_band_mid
  | _ => lbc_band_high
  end.

(* 五层码族的档位读取：每件都是「rewrite lbh_nu2_pairp + 字面计算」——
   标签恒等式（lbh_nu2_pairp : ν₂(pairp a b) = a）一步定档。 *)
Lemma lbc_gnT_band_low : forall t : Term, lbc_band_class (gnT t) = lbc_band_low.
Proof.
  intros t. destruct t as [k| |t'|a b]; unfold lbc_band_class; cbn [gnT];
    rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbc_gnF_band_old : forall g : Formula, lbc_band_class (gnF g) = lbc_band_old.
Proof.
  intros g. destruct g as [u1 u2|a b]; unfold lbc_band_class; cbn [gnF];
    rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbc_gnPrf_band_mid : forall (f : Formula) (pf : Prf f),
  lbc_band_class (gnPrf f pf) = lbc_band_mid.
Proof.
  intros f pf. destruct pf as [u1 u2 Hv | a b pf1 pf2 | th t1 t2 Hv];
    unfold lbc_band_class; cbn [gnPrf]; rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbc_gnF2_band_high : forall f2 : Formula2,
  lbc_band_class (lbe_gnF2 f2) = lbc_band_high.
Proof.
  intros f2. destruct f2 as [g|B c|a b]; unfold lbc_band_class; cbn [lbe_gnF2];
    rewrite lbh_nu2_pairp; reflexivity.
Qed.

Lemma lbc_gnPrf2_band_high : forall (f2 : Formula2) (pf : Prf2 f2),
  lbc_band_class (gnPrf2 f2 pf) = lbc_band_high.
Proof.
  intros f2 pf. destruct pf as
    [g pf0 | a b pf1 pf2 | th t1 t2 Hv | B c g pf0 Hb Hc];
    unfold lbc_band_class; cbn [gnPrf2]; rewrite lbh_nu2_pairp; reflexivity.
Qed.

(* 合成子的档位由构造子决定，与运算对象无关：MP2 合成码（标签 13）
   与界闭包 boxup2（= MPc2 B B）恒在高带——遗传分层的合成封闭性。 *)
Lemma lbc_MPc2_band_high : forall c1 c2 : nat,
  lbc_band_class (MPc2 c1 c2) = lbc_band_high.
Proof.
  intros c1 c2. unfold lbc_band_class, MPc2.
  rewrite lbh_nu2_pairp. reflexivity.
Qed.

Lemma lbc_boxup2_band_high : forall B : nat,
  lbc_band_class (lbg_boxup2 B) = lbc_band_high.
Proof.
  intros B. unfold lbc_band_class, lbg_boxup2, MPc2.
  rewrite lbh_nu2_pairp. reflexivity.
Qed.

(* 对角候选族（Löb 算子 th 的对角句之码）恒在高带 *)
Lemma lbc_diag_band_high : forall th : Formula2,
  lbc_band_class (lbe_gnF2 (lbe_diagF2 th)) = lbc_band_high.
Proof. intros th. exact (lbc_gnF2_band_high (lbe_diagF2 th)). Qed.

(* ===================================================================== *)
(* §B  独立带谓词 × 盒的档位可靠性 × 全谱盲性分类（谱桥主面）                                    *)
(* ===================================================================== *)

(* 独立带谓词：带 k 对旧盒独立 ⟺ k 不是旧带（旧盒在该带恒盲）；
   对新盒独立 ⟺ k 不是高带。 *)
Definition lbc_old_indep (k : lbc_band) : bool :=
  match k with
  | lbc_band_old => false
  | _ => true
  end.

Definition lbc_new_indep (k : lbc_band) : bool :=
  match k with
  | lbc_band_high => false
  | _ => true
  end.

(* ★ C2 档位可靠性（肯定⟹档位）：盒真的反射半边（lbh_box_reflect / lbh_box2_reflect
   给出显式原像见证）× 五层档位读取——肯定域被档位完全锁定。 *)
Theorem lbc_old_box_band_sound : forall (B c : nat),
  lbd_Box B c = true -> lbc_band_class c = lbc_band_old.
Proof.
  intros B c H. destruct (lbh_box_reflect B c H) as [g Hgc]. tidQ Hgc Eg.
  rewrite <- Eg. exact (lbc_gnF_band_old g).
Qed.

Theorem lbc_new_box_band_sound : forall (B c : nat),
  lbg_Box2 B c = true -> lbc_band_class c = lbc_band_high.
Proof.
  intros B c H. destruct (lbh_box2_reflect B c H) as [x Hxc]. tidQ Hxc Ex.
  rewrite <- Ex. exact (lbc_gnF2_band_high x).
Qed.

(* ★ 独立带正确性（档位⟹盲）：独立带谓词取真处盒恒盲——
   可靠性定理的逆否面的肯定形态。 *)
Theorem lbc_old_indep_correct : forall (k : lbc_band) (B c : nat),
  lbc_band_class c = k -> lbc_old_indep k = true -> lbd_Box B c = false.
Proof.
  intros k B c Hclass Hind. destruct (lbd_Box B c) eqn:Eb; [|reflexivity].
  exfalso.
  pose proof (lbc_old_box_band_sound B c Eb) as Hs.
  rewrite Hclass in Hs. rewrite Hs in Hind.
  cbn [lbc_old_indep] in Hind. discriminate Hind.
Qed.

Theorem lbc_new_indep_correct : forall (k : lbc_band) (B c : nat),
  lbc_band_class c = k -> lbc_new_indep k = true -> lbg_Box2 B c = false.
Proof.
  intros k B c Hclass Hind. destruct (lbg_Box2 B c) eqn:Eb; [|reflexivity].
  exfalso.
  pose proof (lbc_new_box_band_sound B c Eb) as Hs.
  rewrite Hclass in Hs. rewrite Hs in Hind.
  cbn [lbc_new_indep] in Hind. discriminate Hind.
Qed.

(* ★ C3 全谱盲性分类（依赖 match 定理）：对一切界与码，两盒的盲性由分类器
   逐档完全决定——低带/证明带对两盒皆盲，旧带仅新盒盲（旧盒可及），
   高带仅旧盒盲（新盒可及）。四档无一悬置。 *)
Theorem lbc_spectral_blind : forall (B c : nat),
  match lbc_band_class c with
  | lbc_band_low => ((lbd_Box B c = false) * (lbg_Box2 B c = false))%type
  | lbc_band_old => lbg_Box2 B c = false
  | lbc_band_mid => ((lbd_Box B c = false) * (lbg_Box2 B c = false))%type
  | lbc_band_high => lbd_Box B c = false
  end.
Proof.
  intros B c. destruct (lbc_band_class c) as [| | |] eqn:Ek; cbv iota.
  - split.
    + destruct (lbd_Box B c) eqn:Eb; [|reflexivity]. exfalso.
      pose proof (lbc_old_box_band_sound B c Eb) as Hs.
      rewrite Ek in Hs. discriminate Hs.
    + destruct (lbg_Box2 B c) eqn:Eb; [|reflexivity]. exfalso.
      pose proof (lbc_new_box_band_sound B c Eb) as Hs.
      rewrite Ek in Hs. discriminate Hs.
  - destruct (lbg_Box2 B c) eqn:Eb; [|reflexivity]. exfalso.
    pose proof (lbc_new_box_band_sound B c Eb) as Hs.
    rewrite Ek in Hs. discriminate Hs.
  - split.
    + destruct (lbd_Box B c) eqn:Eb; [|reflexivity]. exfalso.
      pose proof (lbc_old_box_band_sound B c Eb) as Hs.
      rewrite Ek in Hs. discriminate Hs.
    + destruct (lbg_Box2 B c) eqn:Eb; [|reflexivity]. exfalso.
      pose proof (lbc_new_box_band_sound B c Eb) as Hs.
      rewrite Ek in Hs. discriminate Hs.
  - destruct (lbd_Box B c) eqn:Eb; [|reflexivity]. exfalso.
    pose proof (lbc_old_box_band_sound B c Eb) as Hs.
    rewrite Ek in Hs. discriminate Hs.
Qed.

(* ★ C4 肯定面（非独立带的显式可肯定见证，sigT 载体、loeb_tid 载体、零 Prop）：
   旧带确有旧盒可肯定的码（展品：teq 0 0 的码，界 S(证明码) 闭式给出）；
   高带确有新盒可肯定的码（展品：第一张码级证书化 Σ-原子，界 S(凭证码)）。 *)
Theorem lbc_band_old_affirmable :
  sigT (fun c : nat => sigT (fun B : nat =>
    (loeb_tid lbc_band (lbc_band_class c) lbc_band_old *
     loeb_tid bool (lbd_Box B c) true)%type)%type)%type.
Proof.
  exists (gnF (teq tzero tzero)).
  exists (Datatypes.S (gnPrf (teq tzero tzero) lbf_demo_pf0)).
  split.
  - apply loeb_tid_eq. apply lbc_gnF_band_old.
  - apply loeb_tid_eq.
    exact (lbd_HBL1 (teq tzero tzero) lbf_demo_pf0
             (Datatypes.S (gnPrf (teq tzero tzero) lbf_demo_pf0))
             (Nat.le_refl (Datatypes.S (gnPrf (teq tzero tzero) lbf_demo_pf0)))).
Qed.

Theorem lbc_band_high_affirmable :
  sigT (fun c : nat => sigT (fun B : nat =>
    (loeb_tid lbc_band (lbc_band_class c) lbc_band_high *
     loeb_tid bool (lbg_Box2 B c) true)%type)%type)%type.
Proof.
  exists (lbe_gnF2 lbf_demo_atom).
  exists (Datatypes.S (gnPrf2 lbf_demo_atom lbg_demo_row_code)).
  split.
  - apply loeb_tid_eq. apply lbc_gnF2_band_high.
  - apply loeb_tid_eq.
    exact (lbg_Box2_HBL1 lbf_demo_atom lbg_demo_row_code
             (Datatypes.S (gnPrf2 lbf_demo_atom lbg_demo_row_code))
             (Nat.le_refl (Datatypes.S (gnPrf2 lbf_demo_atom lbg_demo_row_code)))).
Qed.

(* ★ C4 独立带的 sigT 见证：存在带 k——旧盒独立带谓词在 k 取真，
   且一切对角候选 ⌜diag th⌝₂ 的档位皆为 k。对角族整体居住在旧盒的独立带内；
   界与码上的肯定事件在该带不存在（lbc_spectral_blind 高带肢）。 *)
Theorem lbc_indep_band_witness :
  sigT (fun k : lbc_band =>
    ((loeb_tid bool (lbc_old_indep k) true) *
     (forall th : Formula2,
        loeb_tid lbc_band (lbc_band_class (lbe_gnF2 (lbe_diagF2 th))) k))%type)%type.
Proof.
  exists lbc_band_high. split.
  - apply loeb_tid_refl.
  - intros th. apply loeb_tid_eq. apply lbc_diag_band_high.
Qed.

(* ===================================================================== *)
(* §C  σ₈ 分离子的有效应用形：参量化码族上的可计算盲性凭证                                       *)
(* ===================================================================== *)

(* 对角候选族：F2 句 th ↦ 其对角句之码；族上凭证生成器：σ₈∘F。
   凭证的计算量与 lbh_sep 相同（O(ν₂ c) 步可判），假侧即盲性凭证。 *)
Definition lbc_diag_code (th : Formula2) : nat := lbe_gnF2 (lbe_diagF2 th).

Definition lbc_family_cert (F : Formula2 -> nat) (th : Formula2) : bool :=
  lbh_sep (F th).

(* ★ C5 凭证正确性（族无关）：σ₈∘F 在码上取假 ⟹ 该码在一切界下旧盒恒盲
   （使用地基 lbh_sep_blind：盲侧无条件完全性）。 *)
Theorem lbc_family_cert_blind : forall (F : Formula2 -> nat) (th : Formula2) (B : nat),
  lbc_family_cert F th = false -> lbd_Box B (F th) = false.
Proof. intros F th B H. exact (lbh_sep_blind (F th) B H). Qed.

(* ★ C5 对角族上凭证恒假：「对角不动点肯定不存在」逐族有总可计算凭证——
   给定 th，凭证 lbc_family_cert lbc_diag_code th 一步算出 false，
   其盲性推论由 lbc_family_cert_blind 给出。 *)
Theorem lbc_family_diag_separated : forall th : Formula2,
  lbc_family_cert lbc_diag_code th = false.
Proof. intros th. unfold lbc_family_cert, lbc_diag_code. apply lbh_gnF2_sep. Qed.

(* 族级应用封装：凭证值 + 其盲性推论的成对交付 *)
Theorem lbc_family_diag_applied : forall (th : Formula2) (B : nat),
  ((lbc_family_cert lbc_diag_code th = false) *
   (lbd_Box B (lbc_diag_code th) = false))%type.
Proof.
  intros th B. split.
  - apply lbc_family_diag_separated.
  - exact (lbc_family_cert_blind lbc_diag_code th B (lbc_family_diag_separated th)).
Qed.

(* ===================================================================== *)
(* §D  Goodstein 谱面使用主定理：机器层 × 分离层的显式合成                                      *)
(* ===================================================================== *)

(* ★ C6 主定理一（单凭证双盒分离）：任一 Prf2 凭证 pf 同时给出——
   (i) 凭证码的档位（高带：机器层码族 gnPrf2 的 ν₂ ∈ {12..15}）；
   (ii) 目标码的档位（高带：F2 码族 ν₂ ∈ {9,10,11}）；
   (iii) 新盒在闭式界 S(凭证码) 处肯定目标码（机器层 HBL1：凭证即点火）；
   (iv) 旧盒在一切界下盲（分离层：高带恒盲）；
   (v) σ₈ 分离值假（分离层的可计算凭证）。
   一张凭证同时是两盒的档案：对旧盒是分离见证，对新盒是肯定见证。 *)
Theorem lbc_goodstein_split : forall (f2 : Formula2) (pf : Prf2 f2) (B : nat),
  ((lbc_band_class (gnPrf2 f2 pf) = lbc_band_high) *
   ((lbc_band_class (lbe_gnF2 f2) = lbc_band_high) *
    ((lbg_Box2 (Datatypes.S (gnPrf2 f2 pf)) (lbe_gnF2 f2) = true) *
     ((lbd_Box B (lbe_gnF2 f2) = false) *
      (lbh_sep (lbe_gnF2 f2) = false)))))%type.
Proof.
  intros f2 pf B. split.
  - apply lbc_gnPrf2_band_high.
  - split.
    + apply lbc_gnF2_band_high.
    + split.
      * exact (lbg_Box2_HBL1 f2 pf (Datatypes.S (gnPrf2 f2 pf))
                 (Nat.le_refl (Datatypes.S (gnPrf2 f2 pf)))).
      * split.
        -- apply lbh_box_f2_false.
        -- apply lbh_gnF2_sep.
Qed.

(* ★ C6 主定理二（谱面无不动点）：任意 F2 句 g 的档位 k 被分类器算出后，
   定理把 k 钉死为高带，并连带交付 σ₈ 假、旧盒一切界盲、Löb 固定式
   （Σ-槽内置 g 自身码）在一切赋值下恒真——地基 lbh_nofixpoint 的
   逐档升级形：无不动点性现在带档位、分离值、盲性与空洞性四个可计算分量。 *)
Theorem lbc_spectral_nofix : forall (B : nat) (g q : Formula2) (s : nat -> nat)
  (k : lbc_band),
  lbc_band_class (lbe_gnF2 g) = k ->
  ((k = lbc_band_high) *
   ((lbh_sep (lbe_gnF2 g) = false) *
    ((lbd_Box B (lbe_gnF2 g) = false) *
     (evalF2 (fimp2 (fsig (numT B) (numT (lbe_gnF2 g))) q) s = true))))%type.
Proof.
  intros B g q s k Hk. rewrite lbc_gnF2_band_high in Hk.
  split.
  - symmetry. exact Hk.
  - split.
    + apply lbh_gnF2_sep.
    + split.
      * apply lbh_box_f2_false.
      * exact (snd (lbh_nofixpoint B g q s)).
Qed.

(* 展品：第一张码级证书化 Σ-原子（DS 凭证层展品行）过主定理——
   机器层凭证 lbg_demo_row_code 的五重档案在界 3000 处闭式交付。 *)
Theorem lbc_demo_goodstein_row :
  ((lbc_band_class (gnPrf2 lbf_demo_atom lbg_demo_row_code) = lbc_band_high) *
   ((lbc_band_class (lbe_gnF2 lbf_demo_atom) = lbc_band_high) *
    ((lbg_Box2 (Datatypes.S (gnPrf2 lbf_demo_atom lbg_demo_row_code))
        (lbe_gnF2 lbf_demo_atom) = true) *
     ((lbd_Box 3000 (lbe_gnF2 lbf_demo_atom) = false) *
      (lbh_sep (lbe_gnF2 lbf_demo_atom) = false)))))%type.
Proof. exact (lbc_goodstein_split lbf_demo_atom lbg_demo_row_code 3000). Qed.

(* ===================================================================== *)
(* §G  数值验证件（分类器与凭证的 vm_compute 可判性：四档各一 + 对角族展品）                          *)
(* ===================================================================== *)

(* 档位数值四展品：656 = ⌜0=0⌝（ν₂=4，旧带）、2624 = D1 证明码（ν₂=6，证明带）、
   512 = 2⁹（ν₂=9，高带——非任何句之码的高位点）、⌜0⌝（ν₂=1，低带）。 *)
Theorem lbc_demo_band_656 : lbc_band_class 656 = lbc_band_old.
Proof. vm_compute. reflexivity. Qed.

Theorem lbc_demo_band_2624 : lbc_band_class 2624 = lbc_band_mid.
Proof. vm_compute. reflexivity. Qed.

Theorem lbc_demo_band_512 : lbc_band_class 512 = lbc_band_high.
Proof. vm_compute. reflexivity. Qed.

Theorem lbc_demo_band_tzero : lbc_band_class (gnT tzero) = lbc_band_low.
Proof. vm_compute. reflexivity. Qed.

(* 对角族展品（DD 展品句 lbe_demo_th）：其候选码的档位与 σ₈ 凭证
   一律由定理通道交付（vm_compute 独立复核见提取检验）。 *)
Theorem lbc_demo_diag_band : lbc_band_class (lbc_diag_code lbe_demo_th) = lbc_band_high.
Proof. apply lbc_diag_band_high. Qed.

Theorem lbc_demo_diag_cert : lbc_family_cert lbc_diag_code lbe_demo_th = false.
Proof. apply lbc_family_diag_separated. Qed.

(* —— 假设面自审（全部应 Closed under the global context） —— *)
Print Assumptions lbc_gnT_band_low.
Print Assumptions lbc_gnF_band_old.
Print Assumptions lbc_gnPrf_band_mid.
Print Assumptions lbc_gnF2_band_high.
Print Assumptions lbc_gnPrf2_band_high.
Print Assumptions lbc_MPc2_band_high.
Print Assumptions lbc_boxup2_band_high.
Print Assumptions lbc_diag_band_high.
Print Assumptions lbc_old_box_band_sound.
Print Assumptions lbc_new_box_band_sound.
Print Assumptions lbc_old_indep_correct.
Print Assumptions lbc_new_indep_correct.
Print Assumptions lbc_spectral_blind.
Print Assumptions lbc_band_old_affirmable.
Print Assumptions lbc_band_high_affirmable.
Print Assumptions lbc_indep_band_witness.
Print Assumptions lbc_family_cert_blind.
Print Assumptions lbc_family_diag_separated.
Print Assumptions lbc_family_diag_applied.
Print Assumptions lbc_goodstein_split.
Print Assumptions lbc_spectral_nofix.
Print Assumptions lbc_demo_goodstein_row.
Print Assumptions lbc_demo_diag_cert.
