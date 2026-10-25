(* piu_zz_tau_hb_wave1.v — KB11 Hb 升格候选子片 1/8（512 段 Hb0-Hb15·机械升格件·零漂移回读断言已过）。
   使命：consumer 片 assert (HbN : <封闭语句>) + brace 块逐块升格为独立引理（语句/证明体逐字保留，
         抽取器对每生成件回读 diff 断言通过），使 128 小件可全并行独立编译（各自独立进程内存清零），
         替代 20h 单体磨；本件为候选稿，落地须过试炮与终门，不替代正本。
   依赖：piu_zz_tau_enclosure_bank4（Require Export 链末前件，传递覆盖 bank1..bank3 与 base）、
         piu_zz_poincare_engine、piu_zz_padic_clearing、Stdlib QArith/ZArith/Arith/PArith/Lia/List。
   对标：piu_zz_tau_enclosure.v（3275 行 post-fix·原巨件 md5 494c8738 分段账）zzPhi_512 段 L103-L774 /
         zzPhi_1024 段 L1019-L3034 的 assert (HbN) 块逐字升格。
   构造性：本片语句零假设、零公理；语句全封闭（右边=bank 事实闭式积），
         证明体只吃 bank 引理＋cbn＋reflexivity；块间零依赖边（ledger 实测）。
   编译配方: coqc -time -native-compiler no -q -Q . "" piu_zz_tau_hb_wave1.v *)
Require Export piu_zz_tau_enclosure_bank4.
From Stdlib Require Import QArith ZArith Arith PArith Lia List.
Require Import piu_zz_poincare_engine piu_zz_padic_clearing.

(* src piu_zz_tau_enclosure.v L103-L123 (assert Hb0) *)
Lemma piu_zz_hb_512_0 : piu_zz_zprod_seg 512%nat (512%nat + 496%nat) 16%nat = ((if zz_in_Pn 512 1009%nat then Z.of_nat 1009%nat else 1%Z) * ((if zz_in_Pn 512 1010%nat then Z.of_nat 1010%nat else 1%Z) * ((if zz_in_Pn 512 1011%nat then Z.of_nat 1011%nat else 1%Z) * ((if zz_in_Pn 512 1012%nat then Z.of_nat 1012%nat else 1%Z) * ((if zz_in_Pn 512 1013%nat then Z.of_nat 1013%nat else 1%Z) * ((if zz_in_Pn 512 1014%nat then Z.of_nat 1014%nat else 1%Z) * ((if zz_in_Pn 512 1015%nat then Z.of_nat 1015%nat else 1%Z) * ((if zz_in_Pn 512 1016%nat then Z.of_nat 1016%nat else 1%Z) * ((if zz_in_Pn 512 1017%nat then Z.of_nat 1017%nat else 1%Z) * ((if zz_in_Pn 512 1018%nat then Z.of_nat 1018%nat else 1%Z) * ((if zz_in_Pn 512 1019%nat then Z.of_nat 1019%nat else 1%Z) * ((if zz_in_Pn 512 1020%nat then Z.of_nat 1020%nat else 1%Z) * ((if zz_in_Pn 512 1021%nat then Z.of_nat 1021%nat else 1%Z) * ((if zz_in_Pn 512 1022%nat then Z.of_nat 1022%nat else 1%Z) * ((if zz_in_Pn 512 1023%nat then Z.of_nat 1023%nat else 1%Z) * (if zz_in_Pn 512 1024%nat then Z.of_nat 1024%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_1024.
    rewrite piu_zz_inPn_512_1023.
    rewrite piu_zz_inPn_512_1022.
    rewrite piu_zz_inPn_512_1021.
    rewrite piu_zz_inPn_512_1020.
    rewrite piu_zz_inPn_512_1019.
    rewrite piu_zz_inPn_512_1018.
    rewrite piu_zz_inPn_512_1017.
    rewrite piu_zz_inPn_512_1016.
    rewrite piu_zz_inPn_512_1015.
    rewrite piu_zz_inPn_512_1014.
    rewrite piu_zz_inPn_512_1013.
    rewrite piu_zz_inPn_512_1012.
    rewrite piu_zz_inPn_512_1011.
    rewrite piu_zz_inPn_512_1010.
    rewrite piu_zz_inPn_512_1009.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L124-L144 (assert Hb1) *)
Lemma piu_zz_hb_512_1 : piu_zz_zprod_seg 512%nat (512%nat + 480%nat) 16%nat = ((if zz_in_Pn 512 993%nat then Z.of_nat 993%nat else 1%Z) * ((if zz_in_Pn 512 994%nat then Z.of_nat 994%nat else 1%Z) * ((if zz_in_Pn 512 995%nat then Z.of_nat 995%nat else 1%Z) * ((if zz_in_Pn 512 996%nat then Z.of_nat 996%nat else 1%Z) * ((if zz_in_Pn 512 997%nat then Z.of_nat 997%nat else 1%Z) * ((if zz_in_Pn 512 998%nat then Z.of_nat 998%nat else 1%Z) * ((if zz_in_Pn 512 999%nat then Z.of_nat 999%nat else 1%Z) * ((if zz_in_Pn 512 1000%nat then Z.of_nat 1000%nat else 1%Z) * ((if zz_in_Pn 512 1001%nat then Z.of_nat 1001%nat else 1%Z) * ((if zz_in_Pn 512 1002%nat then Z.of_nat 1002%nat else 1%Z) * ((if zz_in_Pn 512 1003%nat then Z.of_nat 1003%nat else 1%Z) * ((if zz_in_Pn 512 1004%nat then Z.of_nat 1004%nat else 1%Z) * ((if zz_in_Pn 512 1005%nat then Z.of_nat 1005%nat else 1%Z) * ((if zz_in_Pn 512 1006%nat then Z.of_nat 1006%nat else 1%Z) * ((if zz_in_Pn 512 1007%nat then Z.of_nat 1007%nat else 1%Z) * (if zz_in_Pn 512 1008%nat then Z.of_nat 1008%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_1008.
    rewrite piu_zz_inPn_512_1007.
    rewrite piu_zz_inPn_512_1006.
    rewrite piu_zz_inPn_512_1005.
    rewrite piu_zz_inPn_512_1004.
    rewrite piu_zz_inPn_512_1003.
    rewrite piu_zz_inPn_512_1002.
    rewrite piu_zz_inPn_512_1001.
    rewrite piu_zz_inPn_512_1000.
    rewrite piu_zz_inPn_512_999.
    rewrite piu_zz_inPn_512_998.
    rewrite piu_zz_inPn_512_997.
    rewrite piu_zz_inPn_512_996.
    rewrite piu_zz_inPn_512_995.
    rewrite piu_zz_inPn_512_994.
    rewrite piu_zz_inPn_512_993.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L145-L165 (assert Hb2) *)
Lemma piu_zz_hb_512_2 : piu_zz_zprod_seg 512%nat (512%nat + 464%nat) 16%nat = ((if zz_in_Pn 512 977%nat then Z.of_nat 977%nat else 1%Z) * ((if zz_in_Pn 512 978%nat then Z.of_nat 978%nat else 1%Z) * ((if zz_in_Pn 512 979%nat then Z.of_nat 979%nat else 1%Z) * ((if zz_in_Pn 512 980%nat then Z.of_nat 980%nat else 1%Z) * ((if zz_in_Pn 512 981%nat then Z.of_nat 981%nat else 1%Z) * ((if zz_in_Pn 512 982%nat then Z.of_nat 982%nat else 1%Z) * ((if zz_in_Pn 512 983%nat then Z.of_nat 983%nat else 1%Z) * ((if zz_in_Pn 512 984%nat then Z.of_nat 984%nat else 1%Z) * ((if zz_in_Pn 512 985%nat then Z.of_nat 985%nat else 1%Z) * ((if zz_in_Pn 512 986%nat then Z.of_nat 986%nat else 1%Z) * ((if zz_in_Pn 512 987%nat then Z.of_nat 987%nat else 1%Z) * ((if zz_in_Pn 512 988%nat then Z.of_nat 988%nat else 1%Z) * ((if zz_in_Pn 512 989%nat then Z.of_nat 989%nat else 1%Z) * ((if zz_in_Pn 512 990%nat then Z.of_nat 990%nat else 1%Z) * ((if zz_in_Pn 512 991%nat then Z.of_nat 991%nat else 1%Z) * (if zz_in_Pn 512 992%nat then Z.of_nat 992%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_992.
    rewrite piu_zz_inPn_512_991.
    rewrite piu_zz_inPn_512_990.
    rewrite piu_zz_inPn_512_989.
    rewrite piu_zz_inPn_512_988.
    rewrite piu_zz_inPn_512_987.
    rewrite piu_zz_inPn_512_986.
    rewrite piu_zz_inPn_512_985.
    rewrite piu_zz_inPn_512_984.
    rewrite piu_zz_inPn_512_983.
    rewrite piu_zz_inPn_512_982.
    rewrite piu_zz_inPn_512_981.
    rewrite piu_zz_inPn_512_980.
    rewrite piu_zz_inPn_512_979.
    rewrite piu_zz_inPn_512_978.
    rewrite piu_zz_inPn_512_977.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L166-L186 (assert Hb3) *)
Lemma piu_zz_hb_512_3 : piu_zz_zprod_seg 512%nat (512%nat + 448%nat) 16%nat = ((if zz_in_Pn 512 961%nat then Z.of_nat 961%nat else 1%Z) * ((if zz_in_Pn 512 962%nat then Z.of_nat 962%nat else 1%Z) * ((if zz_in_Pn 512 963%nat then Z.of_nat 963%nat else 1%Z) * ((if zz_in_Pn 512 964%nat then Z.of_nat 964%nat else 1%Z) * ((if zz_in_Pn 512 965%nat then Z.of_nat 965%nat else 1%Z) * ((if zz_in_Pn 512 966%nat then Z.of_nat 966%nat else 1%Z) * ((if zz_in_Pn 512 967%nat then Z.of_nat 967%nat else 1%Z) * ((if zz_in_Pn 512 968%nat then Z.of_nat 968%nat else 1%Z) * ((if zz_in_Pn 512 969%nat then Z.of_nat 969%nat else 1%Z) * ((if zz_in_Pn 512 970%nat then Z.of_nat 970%nat else 1%Z) * ((if zz_in_Pn 512 971%nat then Z.of_nat 971%nat else 1%Z) * ((if zz_in_Pn 512 972%nat then Z.of_nat 972%nat else 1%Z) * ((if zz_in_Pn 512 973%nat then Z.of_nat 973%nat else 1%Z) * ((if zz_in_Pn 512 974%nat then Z.of_nat 974%nat else 1%Z) * ((if zz_in_Pn 512 975%nat then Z.of_nat 975%nat else 1%Z) * (if zz_in_Pn 512 976%nat then Z.of_nat 976%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_976.
    rewrite piu_zz_inPn_512_975.
    rewrite piu_zz_inPn_512_974.
    rewrite piu_zz_inPn_512_973.
    rewrite piu_zz_inPn_512_972.
    rewrite piu_zz_inPn_512_971.
    rewrite piu_zz_inPn_512_970.
    rewrite piu_zz_inPn_512_969.
    rewrite piu_zz_inPn_512_968.
    rewrite piu_zz_inPn_512_967.
    rewrite piu_zz_inPn_512_966.
    rewrite piu_zz_inPn_512_965.
    rewrite piu_zz_inPn_512_964.
    rewrite piu_zz_inPn_512_963.
    rewrite piu_zz_inPn_512_962.
    rewrite piu_zz_inPn_512_961.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L187-L207 (assert Hb4) *)
Lemma piu_zz_hb_512_4 : piu_zz_zprod_seg 512%nat (512%nat + 432%nat) 16%nat = ((if zz_in_Pn 512 945%nat then Z.of_nat 945%nat else 1%Z) * ((if zz_in_Pn 512 946%nat then Z.of_nat 946%nat else 1%Z) * ((if zz_in_Pn 512 947%nat then Z.of_nat 947%nat else 1%Z) * ((if zz_in_Pn 512 948%nat then Z.of_nat 948%nat else 1%Z) * ((if zz_in_Pn 512 949%nat then Z.of_nat 949%nat else 1%Z) * ((if zz_in_Pn 512 950%nat then Z.of_nat 950%nat else 1%Z) * ((if zz_in_Pn 512 951%nat then Z.of_nat 951%nat else 1%Z) * ((if zz_in_Pn 512 952%nat then Z.of_nat 952%nat else 1%Z) * ((if zz_in_Pn 512 953%nat then Z.of_nat 953%nat else 1%Z) * ((if zz_in_Pn 512 954%nat then Z.of_nat 954%nat else 1%Z) * ((if zz_in_Pn 512 955%nat then Z.of_nat 955%nat else 1%Z) * ((if zz_in_Pn 512 956%nat then Z.of_nat 956%nat else 1%Z) * ((if zz_in_Pn 512 957%nat then Z.of_nat 957%nat else 1%Z) * ((if zz_in_Pn 512 958%nat then Z.of_nat 958%nat else 1%Z) * ((if zz_in_Pn 512 959%nat then Z.of_nat 959%nat else 1%Z) * (if zz_in_Pn 512 960%nat then Z.of_nat 960%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_960.
    rewrite piu_zz_inPn_512_959.
    rewrite piu_zz_inPn_512_958.
    rewrite piu_zz_inPn_512_957.
    rewrite piu_zz_inPn_512_956.
    rewrite piu_zz_inPn_512_955.
    rewrite piu_zz_inPn_512_954.
    rewrite piu_zz_inPn_512_953.
    rewrite piu_zz_inPn_512_952.
    rewrite piu_zz_inPn_512_951.
    rewrite piu_zz_inPn_512_950.
    rewrite piu_zz_inPn_512_949.
    rewrite piu_zz_inPn_512_948.
    rewrite piu_zz_inPn_512_947.
    rewrite piu_zz_inPn_512_946.
    rewrite piu_zz_inPn_512_945.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L208-L228 (assert Hb5) *)
Lemma piu_zz_hb_512_5 : piu_zz_zprod_seg 512%nat (512%nat + 416%nat) 16%nat = ((if zz_in_Pn 512 929%nat then Z.of_nat 929%nat else 1%Z) * ((if zz_in_Pn 512 930%nat then Z.of_nat 930%nat else 1%Z) * ((if zz_in_Pn 512 931%nat then Z.of_nat 931%nat else 1%Z) * ((if zz_in_Pn 512 932%nat then Z.of_nat 932%nat else 1%Z) * ((if zz_in_Pn 512 933%nat then Z.of_nat 933%nat else 1%Z) * ((if zz_in_Pn 512 934%nat then Z.of_nat 934%nat else 1%Z) * ((if zz_in_Pn 512 935%nat then Z.of_nat 935%nat else 1%Z) * ((if zz_in_Pn 512 936%nat then Z.of_nat 936%nat else 1%Z) * ((if zz_in_Pn 512 937%nat then Z.of_nat 937%nat else 1%Z) * ((if zz_in_Pn 512 938%nat then Z.of_nat 938%nat else 1%Z) * ((if zz_in_Pn 512 939%nat then Z.of_nat 939%nat else 1%Z) * ((if zz_in_Pn 512 940%nat then Z.of_nat 940%nat else 1%Z) * ((if zz_in_Pn 512 941%nat then Z.of_nat 941%nat else 1%Z) * ((if zz_in_Pn 512 942%nat then Z.of_nat 942%nat else 1%Z) * ((if zz_in_Pn 512 943%nat then Z.of_nat 943%nat else 1%Z) * (if zz_in_Pn 512 944%nat then Z.of_nat 944%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_944.
    rewrite piu_zz_inPn_512_943.
    rewrite piu_zz_inPn_512_942.
    rewrite piu_zz_inPn_512_941.
    rewrite piu_zz_inPn_512_940.
    rewrite piu_zz_inPn_512_939.
    rewrite piu_zz_inPn_512_938.
    rewrite piu_zz_inPn_512_937.
    rewrite piu_zz_inPn_512_936.
    rewrite piu_zz_inPn_512_935.
    rewrite piu_zz_inPn_512_934.
    rewrite piu_zz_inPn_512_933.
    rewrite piu_zz_inPn_512_932.
    rewrite piu_zz_inPn_512_931.
    rewrite piu_zz_inPn_512_930.
    rewrite piu_zz_inPn_512_929.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L229-L249 (assert Hb6) *)
Lemma piu_zz_hb_512_6 : piu_zz_zprod_seg 512%nat (512%nat + 400%nat) 16%nat = ((if zz_in_Pn 512 913%nat then Z.of_nat 913%nat else 1%Z) * ((if zz_in_Pn 512 914%nat then Z.of_nat 914%nat else 1%Z) * ((if zz_in_Pn 512 915%nat then Z.of_nat 915%nat else 1%Z) * ((if zz_in_Pn 512 916%nat then Z.of_nat 916%nat else 1%Z) * ((if zz_in_Pn 512 917%nat then Z.of_nat 917%nat else 1%Z) * ((if zz_in_Pn 512 918%nat then Z.of_nat 918%nat else 1%Z) * ((if zz_in_Pn 512 919%nat then Z.of_nat 919%nat else 1%Z) * ((if zz_in_Pn 512 920%nat then Z.of_nat 920%nat else 1%Z) * ((if zz_in_Pn 512 921%nat then Z.of_nat 921%nat else 1%Z) * ((if zz_in_Pn 512 922%nat then Z.of_nat 922%nat else 1%Z) * ((if zz_in_Pn 512 923%nat then Z.of_nat 923%nat else 1%Z) * ((if zz_in_Pn 512 924%nat then Z.of_nat 924%nat else 1%Z) * ((if zz_in_Pn 512 925%nat then Z.of_nat 925%nat else 1%Z) * ((if zz_in_Pn 512 926%nat then Z.of_nat 926%nat else 1%Z) * ((if zz_in_Pn 512 927%nat then Z.of_nat 927%nat else 1%Z) * (if zz_in_Pn 512 928%nat then Z.of_nat 928%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_928.
    rewrite piu_zz_inPn_512_927.
    rewrite piu_zz_inPn_512_926.
    rewrite piu_zz_inPn_512_925.
    rewrite piu_zz_inPn_512_924.
    rewrite piu_zz_inPn_512_923.
    rewrite piu_zz_inPn_512_922.
    rewrite piu_zz_inPn_512_921.
    rewrite piu_zz_inPn_512_920.
    rewrite piu_zz_inPn_512_919.
    rewrite piu_zz_inPn_512_918.
    rewrite piu_zz_inPn_512_917.
    rewrite piu_zz_inPn_512_916.
    rewrite piu_zz_inPn_512_915.
    rewrite piu_zz_inPn_512_914.
    rewrite piu_zz_inPn_512_913.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L250-L270 (assert Hb7) *)
Lemma piu_zz_hb_512_7 : piu_zz_zprod_seg 512%nat (512%nat + 384%nat) 16%nat = ((if zz_in_Pn 512 897%nat then Z.of_nat 897%nat else 1%Z) * ((if zz_in_Pn 512 898%nat then Z.of_nat 898%nat else 1%Z) * ((if zz_in_Pn 512 899%nat then Z.of_nat 899%nat else 1%Z) * ((if zz_in_Pn 512 900%nat then Z.of_nat 900%nat else 1%Z) * ((if zz_in_Pn 512 901%nat then Z.of_nat 901%nat else 1%Z) * ((if zz_in_Pn 512 902%nat then Z.of_nat 902%nat else 1%Z) * ((if zz_in_Pn 512 903%nat then Z.of_nat 903%nat else 1%Z) * ((if zz_in_Pn 512 904%nat then Z.of_nat 904%nat else 1%Z) * ((if zz_in_Pn 512 905%nat then Z.of_nat 905%nat else 1%Z) * ((if zz_in_Pn 512 906%nat then Z.of_nat 906%nat else 1%Z) * ((if zz_in_Pn 512 907%nat then Z.of_nat 907%nat else 1%Z) * ((if zz_in_Pn 512 908%nat then Z.of_nat 908%nat else 1%Z) * ((if zz_in_Pn 512 909%nat then Z.of_nat 909%nat else 1%Z) * ((if zz_in_Pn 512 910%nat then Z.of_nat 910%nat else 1%Z) * ((if zz_in_Pn 512 911%nat then Z.of_nat 911%nat else 1%Z) * (if zz_in_Pn 512 912%nat then Z.of_nat 912%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_912.
    rewrite piu_zz_inPn_512_911.
    rewrite piu_zz_inPn_512_910.
    rewrite piu_zz_inPn_512_909.
    rewrite piu_zz_inPn_512_908.
    rewrite piu_zz_inPn_512_907.
    rewrite piu_zz_inPn_512_906.
    rewrite piu_zz_inPn_512_905.
    rewrite piu_zz_inPn_512_904.
    rewrite piu_zz_inPn_512_903.
    rewrite piu_zz_inPn_512_902.
    rewrite piu_zz_inPn_512_901.
    rewrite piu_zz_inPn_512_900.
    rewrite piu_zz_inPn_512_899.
    rewrite piu_zz_inPn_512_898.
    rewrite piu_zz_inPn_512_897.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L271-L291 (assert Hb8) *)
Lemma piu_zz_hb_512_8 : piu_zz_zprod_seg 512%nat (512%nat + 368%nat) 16%nat = ((if zz_in_Pn 512 881%nat then Z.of_nat 881%nat else 1%Z) * ((if zz_in_Pn 512 882%nat then Z.of_nat 882%nat else 1%Z) * ((if zz_in_Pn 512 883%nat then Z.of_nat 883%nat else 1%Z) * ((if zz_in_Pn 512 884%nat then Z.of_nat 884%nat else 1%Z) * ((if zz_in_Pn 512 885%nat then Z.of_nat 885%nat else 1%Z) * ((if zz_in_Pn 512 886%nat then Z.of_nat 886%nat else 1%Z) * ((if zz_in_Pn 512 887%nat then Z.of_nat 887%nat else 1%Z) * ((if zz_in_Pn 512 888%nat then Z.of_nat 888%nat else 1%Z) * ((if zz_in_Pn 512 889%nat then Z.of_nat 889%nat else 1%Z) * ((if zz_in_Pn 512 890%nat then Z.of_nat 890%nat else 1%Z) * ((if zz_in_Pn 512 891%nat then Z.of_nat 891%nat else 1%Z) * ((if zz_in_Pn 512 892%nat then Z.of_nat 892%nat else 1%Z) * ((if zz_in_Pn 512 893%nat then Z.of_nat 893%nat else 1%Z) * ((if zz_in_Pn 512 894%nat then Z.of_nat 894%nat else 1%Z) * ((if zz_in_Pn 512 895%nat then Z.of_nat 895%nat else 1%Z) * (if zz_in_Pn 512 896%nat then Z.of_nat 896%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_896.
    rewrite piu_zz_inPn_512_895.
    rewrite piu_zz_inPn_512_894.
    rewrite piu_zz_inPn_512_893.
    rewrite piu_zz_inPn_512_892.
    rewrite piu_zz_inPn_512_891.
    rewrite piu_zz_inPn_512_890.
    rewrite piu_zz_inPn_512_889.
    rewrite piu_zz_inPn_512_888.
    rewrite piu_zz_inPn_512_887.
    rewrite piu_zz_inPn_512_886.
    rewrite piu_zz_inPn_512_885.
    rewrite piu_zz_inPn_512_884.
    rewrite piu_zz_inPn_512_883.
    rewrite piu_zz_inPn_512_882.
    rewrite piu_zz_inPn_512_881.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L292-L312 (assert Hb9) *)
Lemma piu_zz_hb_512_9 : piu_zz_zprod_seg 512%nat (512%nat + 352%nat) 16%nat = ((if zz_in_Pn 512 865%nat then Z.of_nat 865%nat else 1%Z) * ((if zz_in_Pn 512 866%nat then Z.of_nat 866%nat else 1%Z) * ((if zz_in_Pn 512 867%nat then Z.of_nat 867%nat else 1%Z) * ((if zz_in_Pn 512 868%nat then Z.of_nat 868%nat else 1%Z) * ((if zz_in_Pn 512 869%nat then Z.of_nat 869%nat else 1%Z) * ((if zz_in_Pn 512 870%nat then Z.of_nat 870%nat else 1%Z) * ((if zz_in_Pn 512 871%nat then Z.of_nat 871%nat else 1%Z) * ((if zz_in_Pn 512 872%nat then Z.of_nat 872%nat else 1%Z) * ((if zz_in_Pn 512 873%nat then Z.of_nat 873%nat else 1%Z) * ((if zz_in_Pn 512 874%nat then Z.of_nat 874%nat else 1%Z) * ((if zz_in_Pn 512 875%nat then Z.of_nat 875%nat else 1%Z) * ((if zz_in_Pn 512 876%nat then Z.of_nat 876%nat else 1%Z) * ((if zz_in_Pn 512 877%nat then Z.of_nat 877%nat else 1%Z) * ((if zz_in_Pn 512 878%nat then Z.of_nat 878%nat else 1%Z) * ((if zz_in_Pn 512 879%nat then Z.of_nat 879%nat else 1%Z) * (if zz_in_Pn 512 880%nat then Z.of_nat 880%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_880.
    rewrite piu_zz_inPn_512_879.
    rewrite piu_zz_inPn_512_878.
    rewrite piu_zz_inPn_512_877.
    rewrite piu_zz_inPn_512_876.
    rewrite piu_zz_inPn_512_875.
    rewrite piu_zz_inPn_512_874.
    rewrite piu_zz_inPn_512_873.
    rewrite piu_zz_inPn_512_872.
    rewrite piu_zz_inPn_512_871.
    rewrite piu_zz_inPn_512_870.
    rewrite piu_zz_inPn_512_869.
    rewrite piu_zz_inPn_512_868.
    rewrite piu_zz_inPn_512_867.
    rewrite piu_zz_inPn_512_866.
    rewrite piu_zz_inPn_512_865.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L313-L333 (assert Hb10) *)
Lemma piu_zz_hb_512_10 : piu_zz_zprod_seg 512%nat (512%nat + 336%nat) 16%nat = ((if zz_in_Pn 512 849%nat then Z.of_nat 849%nat else 1%Z) * ((if zz_in_Pn 512 850%nat then Z.of_nat 850%nat else 1%Z) * ((if zz_in_Pn 512 851%nat then Z.of_nat 851%nat else 1%Z) * ((if zz_in_Pn 512 852%nat then Z.of_nat 852%nat else 1%Z) * ((if zz_in_Pn 512 853%nat then Z.of_nat 853%nat else 1%Z) * ((if zz_in_Pn 512 854%nat then Z.of_nat 854%nat else 1%Z) * ((if zz_in_Pn 512 855%nat then Z.of_nat 855%nat else 1%Z) * ((if zz_in_Pn 512 856%nat then Z.of_nat 856%nat else 1%Z) * ((if zz_in_Pn 512 857%nat then Z.of_nat 857%nat else 1%Z) * ((if zz_in_Pn 512 858%nat then Z.of_nat 858%nat else 1%Z) * ((if zz_in_Pn 512 859%nat then Z.of_nat 859%nat else 1%Z) * ((if zz_in_Pn 512 860%nat then Z.of_nat 860%nat else 1%Z) * ((if zz_in_Pn 512 861%nat then Z.of_nat 861%nat else 1%Z) * ((if zz_in_Pn 512 862%nat then Z.of_nat 862%nat else 1%Z) * ((if zz_in_Pn 512 863%nat then Z.of_nat 863%nat else 1%Z) * (if zz_in_Pn 512 864%nat then Z.of_nat 864%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_864.
    rewrite piu_zz_inPn_512_863.
    rewrite piu_zz_inPn_512_862.
    rewrite piu_zz_inPn_512_861.
    rewrite piu_zz_inPn_512_860.
    rewrite piu_zz_inPn_512_859.
    rewrite piu_zz_inPn_512_858.
    rewrite piu_zz_inPn_512_857.
    rewrite piu_zz_inPn_512_856.
    rewrite piu_zz_inPn_512_855.
    rewrite piu_zz_inPn_512_854.
    rewrite piu_zz_inPn_512_853.
    rewrite piu_zz_inPn_512_852.
    rewrite piu_zz_inPn_512_851.
    rewrite piu_zz_inPn_512_850.
    rewrite piu_zz_inPn_512_849.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L334-L354 (assert Hb11) *)
Lemma piu_zz_hb_512_11 : piu_zz_zprod_seg 512%nat (512%nat + 320%nat) 16%nat = ((if zz_in_Pn 512 833%nat then Z.of_nat 833%nat else 1%Z) * ((if zz_in_Pn 512 834%nat then Z.of_nat 834%nat else 1%Z) * ((if zz_in_Pn 512 835%nat then Z.of_nat 835%nat else 1%Z) * ((if zz_in_Pn 512 836%nat then Z.of_nat 836%nat else 1%Z) * ((if zz_in_Pn 512 837%nat then Z.of_nat 837%nat else 1%Z) * ((if zz_in_Pn 512 838%nat then Z.of_nat 838%nat else 1%Z) * ((if zz_in_Pn 512 839%nat then Z.of_nat 839%nat else 1%Z) * ((if zz_in_Pn 512 840%nat then Z.of_nat 840%nat else 1%Z) * ((if zz_in_Pn 512 841%nat then Z.of_nat 841%nat else 1%Z) * ((if zz_in_Pn 512 842%nat then Z.of_nat 842%nat else 1%Z) * ((if zz_in_Pn 512 843%nat then Z.of_nat 843%nat else 1%Z) * ((if zz_in_Pn 512 844%nat then Z.of_nat 844%nat else 1%Z) * ((if zz_in_Pn 512 845%nat then Z.of_nat 845%nat else 1%Z) * ((if zz_in_Pn 512 846%nat then Z.of_nat 846%nat else 1%Z) * ((if zz_in_Pn 512 847%nat then Z.of_nat 847%nat else 1%Z) * (if zz_in_Pn 512 848%nat then Z.of_nat 848%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_848.
    rewrite piu_zz_inPn_512_847.
    rewrite piu_zz_inPn_512_846.
    rewrite piu_zz_inPn_512_845.
    rewrite piu_zz_inPn_512_844.
    rewrite piu_zz_inPn_512_843.
    rewrite piu_zz_inPn_512_842.
    rewrite piu_zz_inPn_512_841.
    rewrite piu_zz_inPn_512_840.
    rewrite piu_zz_inPn_512_839.
    rewrite piu_zz_inPn_512_838.
    rewrite piu_zz_inPn_512_837.
    rewrite piu_zz_inPn_512_836.
    rewrite piu_zz_inPn_512_835.
    rewrite piu_zz_inPn_512_834.
    rewrite piu_zz_inPn_512_833.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L355-L375 (assert Hb12) *)
Lemma piu_zz_hb_512_12 : piu_zz_zprod_seg 512%nat (512%nat + 304%nat) 16%nat = ((if zz_in_Pn 512 817%nat then Z.of_nat 817%nat else 1%Z) * ((if zz_in_Pn 512 818%nat then Z.of_nat 818%nat else 1%Z) * ((if zz_in_Pn 512 819%nat then Z.of_nat 819%nat else 1%Z) * ((if zz_in_Pn 512 820%nat then Z.of_nat 820%nat else 1%Z) * ((if zz_in_Pn 512 821%nat then Z.of_nat 821%nat else 1%Z) * ((if zz_in_Pn 512 822%nat then Z.of_nat 822%nat else 1%Z) * ((if zz_in_Pn 512 823%nat then Z.of_nat 823%nat else 1%Z) * ((if zz_in_Pn 512 824%nat then Z.of_nat 824%nat else 1%Z) * ((if zz_in_Pn 512 825%nat then Z.of_nat 825%nat else 1%Z) * ((if zz_in_Pn 512 826%nat then Z.of_nat 826%nat else 1%Z) * ((if zz_in_Pn 512 827%nat then Z.of_nat 827%nat else 1%Z) * ((if zz_in_Pn 512 828%nat then Z.of_nat 828%nat else 1%Z) * ((if zz_in_Pn 512 829%nat then Z.of_nat 829%nat else 1%Z) * ((if zz_in_Pn 512 830%nat then Z.of_nat 830%nat else 1%Z) * ((if zz_in_Pn 512 831%nat then Z.of_nat 831%nat else 1%Z) * (if zz_in_Pn 512 832%nat then Z.of_nat 832%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_832.
    rewrite piu_zz_inPn_512_831.
    rewrite piu_zz_inPn_512_830.
    rewrite piu_zz_inPn_512_829.
    rewrite piu_zz_inPn_512_828.
    rewrite piu_zz_inPn_512_827.
    rewrite piu_zz_inPn_512_826.
    rewrite piu_zz_inPn_512_825.
    rewrite piu_zz_inPn_512_824.
    rewrite piu_zz_inPn_512_823.
    rewrite piu_zz_inPn_512_822.
    rewrite piu_zz_inPn_512_821.
    rewrite piu_zz_inPn_512_820.
    rewrite piu_zz_inPn_512_819.
    rewrite piu_zz_inPn_512_818.
    rewrite piu_zz_inPn_512_817.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L376-L396 (assert Hb13) *)
Lemma piu_zz_hb_512_13 : piu_zz_zprod_seg 512%nat (512%nat + 288%nat) 16%nat = ((if zz_in_Pn 512 801%nat then Z.of_nat 801%nat else 1%Z) * ((if zz_in_Pn 512 802%nat then Z.of_nat 802%nat else 1%Z) * ((if zz_in_Pn 512 803%nat then Z.of_nat 803%nat else 1%Z) * ((if zz_in_Pn 512 804%nat then Z.of_nat 804%nat else 1%Z) * ((if zz_in_Pn 512 805%nat then Z.of_nat 805%nat else 1%Z) * ((if zz_in_Pn 512 806%nat then Z.of_nat 806%nat else 1%Z) * ((if zz_in_Pn 512 807%nat then Z.of_nat 807%nat else 1%Z) * ((if zz_in_Pn 512 808%nat then Z.of_nat 808%nat else 1%Z) * ((if zz_in_Pn 512 809%nat then Z.of_nat 809%nat else 1%Z) * ((if zz_in_Pn 512 810%nat then Z.of_nat 810%nat else 1%Z) * ((if zz_in_Pn 512 811%nat then Z.of_nat 811%nat else 1%Z) * ((if zz_in_Pn 512 812%nat then Z.of_nat 812%nat else 1%Z) * ((if zz_in_Pn 512 813%nat then Z.of_nat 813%nat else 1%Z) * ((if zz_in_Pn 512 814%nat then Z.of_nat 814%nat else 1%Z) * ((if zz_in_Pn 512 815%nat then Z.of_nat 815%nat else 1%Z) * (if zz_in_Pn 512 816%nat then Z.of_nat 816%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_816.
    rewrite piu_zz_inPn_512_815.
    rewrite piu_zz_inPn_512_814.
    rewrite piu_zz_inPn_512_813.
    rewrite piu_zz_inPn_512_812.
    rewrite piu_zz_inPn_512_811.
    rewrite piu_zz_inPn_512_810.
    rewrite piu_zz_inPn_512_809.
    rewrite piu_zz_inPn_512_808.
    rewrite piu_zz_inPn_512_807.
    rewrite piu_zz_inPn_512_806.
    rewrite piu_zz_inPn_512_805.
    rewrite piu_zz_inPn_512_804.
    rewrite piu_zz_inPn_512_803.
    rewrite piu_zz_inPn_512_802.
    rewrite piu_zz_inPn_512_801.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L397-L417 (assert Hb14) *)
Lemma piu_zz_hb_512_14 : piu_zz_zprod_seg 512%nat (512%nat + 272%nat) 16%nat = ((if zz_in_Pn 512 785%nat then Z.of_nat 785%nat else 1%Z) * ((if zz_in_Pn 512 786%nat then Z.of_nat 786%nat else 1%Z) * ((if zz_in_Pn 512 787%nat then Z.of_nat 787%nat else 1%Z) * ((if zz_in_Pn 512 788%nat then Z.of_nat 788%nat else 1%Z) * ((if zz_in_Pn 512 789%nat then Z.of_nat 789%nat else 1%Z) * ((if zz_in_Pn 512 790%nat then Z.of_nat 790%nat else 1%Z) * ((if zz_in_Pn 512 791%nat then Z.of_nat 791%nat else 1%Z) * ((if zz_in_Pn 512 792%nat then Z.of_nat 792%nat else 1%Z) * ((if zz_in_Pn 512 793%nat then Z.of_nat 793%nat else 1%Z) * ((if zz_in_Pn 512 794%nat then Z.of_nat 794%nat else 1%Z) * ((if zz_in_Pn 512 795%nat then Z.of_nat 795%nat else 1%Z) * ((if zz_in_Pn 512 796%nat then Z.of_nat 796%nat else 1%Z) * ((if zz_in_Pn 512 797%nat then Z.of_nat 797%nat else 1%Z) * ((if zz_in_Pn 512 798%nat then Z.of_nat 798%nat else 1%Z) * ((if zz_in_Pn 512 799%nat then Z.of_nat 799%nat else 1%Z) * (if zz_in_Pn 512 800%nat then Z.of_nat 800%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_800.
    rewrite piu_zz_inPn_512_799.
    rewrite piu_zz_inPn_512_798.
    rewrite piu_zz_inPn_512_797.
    rewrite piu_zz_inPn_512_796.
    rewrite piu_zz_inPn_512_795.
    rewrite piu_zz_inPn_512_794.
    rewrite piu_zz_inPn_512_793.
    rewrite piu_zz_inPn_512_792.
    rewrite piu_zz_inPn_512_791.
    rewrite piu_zz_inPn_512_790.
    rewrite piu_zz_inPn_512_789.
    rewrite piu_zz_inPn_512_788.
    rewrite piu_zz_inPn_512_787.
    rewrite piu_zz_inPn_512_786.
    rewrite piu_zz_inPn_512_785.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.

(* src piu_zz_tau_enclosure.v L418-L438 (assert Hb15) *)
Lemma piu_zz_hb_512_15 : piu_zz_zprod_seg 512%nat (512%nat + 256%nat) 16%nat = ((if zz_in_Pn 512 769%nat then Z.of_nat 769%nat else 1%Z) * ((if zz_in_Pn 512 770%nat then Z.of_nat 770%nat else 1%Z) * ((if zz_in_Pn 512 771%nat then Z.of_nat 771%nat else 1%Z) * ((if zz_in_Pn 512 772%nat then Z.of_nat 772%nat else 1%Z) * ((if zz_in_Pn 512 773%nat then Z.of_nat 773%nat else 1%Z) * ((if zz_in_Pn 512 774%nat then Z.of_nat 774%nat else 1%Z) * ((if zz_in_Pn 512 775%nat then Z.of_nat 775%nat else 1%Z) * ((if zz_in_Pn 512 776%nat then Z.of_nat 776%nat else 1%Z) * ((if zz_in_Pn 512 777%nat then Z.of_nat 777%nat else 1%Z) * ((if zz_in_Pn 512 778%nat then Z.of_nat 778%nat else 1%Z) * ((if zz_in_Pn 512 779%nat then Z.of_nat 779%nat else 1%Z) * ((if zz_in_Pn 512 780%nat then Z.of_nat 780%nat else 1%Z) * ((if zz_in_Pn 512 781%nat then Z.of_nat 781%nat else 1%Z) * ((if zz_in_Pn 512 782%nat then Z.of_nat 782%nat else 1%Z) * ((if zz_in_Pn 512 783%nat then Z.of_nat 783%nat else 1%Z) * (if zz_in_Pn 512 784%nat then Z.of_nat 784%nat else 1%Z)))))))))))))))).
Proof.
    cbn [piu_zz_zprod_seg].
    rewrite piu_zz_inPn_512_784.
    rewrite piu_zz_inPn_512_783.
    rewrite piu_zz_inPn_512_782.
    rewrite piu_zz_inPn_512_781.
    rewrite piu_zz_inPn_512_780.
    rewrite piu_zz_inPn_512_779.
    rewrite piu_zz_inPn_512_778.
    rewrite piu_zz_inPn_512_777.
    rewrite piu_zz_inPn_512_776.
    rewrite piu_zz_inPn_512_775.
    rewrite piu_zz_inPn_512_774.
    rewrite piu_zz_inPn_512_773.
    rewrite piu_zz_inPn_512_772.
    rewrite piu_zz_inPn_512_771.
    rewrite piu_zz_inPn_512_770.
    rewrite piu_zz_inPn_512_769.
    cbn [piu_zz_zprod_seg]. reflexivity.
Qed.
