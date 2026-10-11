(* 模块：tlw1703_uacm_combo_unconditional.v —— pi 几何分离组合件的无条件形。
   数学使命：uacm_pi_strong_sep_combo（uacm_pi_strong_sep_combo.v :229）的
   命中前提 leiblw_Id (lw5n_sep_dec (a/b) (lw5n_nsep (a/b))) true 系旧预算
   lw5n_bnd 足用性承载的假设位（该预算对分离见证不足用：22/7 落窗全程耗尽
   的机器否证见 NsepBudgetExhaustion.v）。本件以换基搜索器替换搜索组件：
   命中级取 tlw1448_nsep_rebase tlw1448_ck (a/b)，其命中由闭合定理链无条件
   供给（tlw1703_rebase_hit_unconditional），经换算引理 uacm_guard_of_hit
   （对任意 q 与任意命中级 n 成立·与具体搜索组件解耦）引出窗距守卫包，交
   守卫形分离定理 leibsep_pi_sep_alpha_guarded，产出显式分离见证：对每一
   非零分母有理数 a/b 存在 0 < c < |pi_geom − a/b|，语句面零前提位。
   依赖清单：Stdlib QArith/Qabs；S01_BaseRing（NatLe/NatLe_drop/real_lt）；
   S02_CauchyComplete（QltT）；S03_QExp（real_metric/real_const）；
   S10_KVQuantTrig（real_pi_geom）；LW0LeibWindow（leiblw_Id）；
   LW0MLicBridge（lw0m_xL/lw0m_e）；LW5SepComplexity（lw5n_sep_dec）；
   tlw1448_rebase（tlw1448_nsep_rebase）；tlw1448_transfer（tlw1448_ck）；
   tlw1703_nsep_minimal_bexp（tlw1703_rebase_hit_unconditional）；
   uacm_pi_strong_sep_combo（uacm_guard_of_hit）；
   Local.LW0LeibSeparation（leibsep_pi_sep_alpha_guarded）。
   对标行：uacm_pi_strong_sep_combo.v :229（守卫形组合件原形·本件为其无
   条件形·搜索组件替换为换基搜索器）；tlw1703_nsep_minimal_bexp.v（命中
   前提的无条件供给）；tlw1459_fold.v :42（闭合定理·命中存在性之根）。
   构造性注记：全 Set/Type 层；零 Axiom/Admitted；零经典逻辑；结论位承载
   于 sigT/And:=prod/QltT/real_lt；证明体为供给-消去-直取的簿记合成链
   （命中供给→守卫包消去→守卫形分离定理直取）；提取面 Obj.magic=0；
   文末 Print Assumptions Closed。
   编译配方：coqc -native-compiler no -q -Q . "" tlw1703_uacm_combo_unconditional.v
   （双 export COQLIB/ROCQLIB；工作目录为认证 vo 播种闭包）。
*)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.
Require Import LW0LeibWindow.
Require Import LW0MLicBridge.
Require Import LW5SepComplexity.
Require Import tlw1448_rebase.
Require Import tlw1448_transfer.
Require Import tlw1703_nsep_minimal_bexp.
Require Import uacm_pi_strong_sep_combo.
Require Import Local.LW0LeibSeparation.

(* 无条件组合件：命中假设位移除——搜索组件为换基搜索器，命中由闭合定理链供给 *)
Theorem uacm_pi_strong_sep_combo_unconditional :
  forall (a b : Q),
    QltT 0 (Qabs b) ->
    sigT (fun c : Q => And (QltT 0 c)
            (real_lt (real_const c)
               (real_metric real_pi_geom (real_const (a / b))))).
Proof.
  intros a b Hb.
  pose proof (tlw1703_rebase_hit_unconditional (a / b)%Q) as Hhit.
  destruct (uacm_guard_of_hit (a / b)%Q
              (tlw1448_nsep_rebase tlw1448_ck (a / b)%Q) Hhit)
    as [N [c0 [Hc0 [HNle Hg]]]].
  exact (leibsep_pi_sep_alpha_guarded a b N c0 Hb
           (NatLe_drop 1 N HNle) Hc0 Hg).
Qed.

(* ---- 假设审计（应全 Closed）---- *)
Print Assumptions uacm_pi_strong_sep_combo_unconditional.

(* ---- 提取检验（Obj.magic 应为 0）---- *)
From Stdlib Require Import Extraction.
Extraction "tlw1703_uacm_ext.ml" tlw1448_ck tlw1448_nsep_rebase
  uacm_pi_strong_sep_combo_unconditional.
