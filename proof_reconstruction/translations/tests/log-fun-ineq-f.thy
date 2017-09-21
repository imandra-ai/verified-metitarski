theory "log-fun-ineq-f"
  imports "../GenerateATP"
begin
  
lemma "\<forall>(X::real).(\<forall>(A::real).
  (((Not((A <= 0)) \<and> (Not((X <= 0)) \<and> Not((4 <= X)))) --> 
      (ln(X) <= (1 + ((exp((ln(X) / A)) * A) / exp(1)))))))"  
  apply(tactic {*fn st => (writeln (isar_proof st [] @{context}); Seq.single st) *})
proof -
  { fix rr :: real and rra :: real
    have ff1: "- 1 + rr < rra * - 1 * rr \<or> rra * - 1 \<le> (- 1 + rr) / rr \<or> rr \<le> 0"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff2: "- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < 21743271936 / 7992538801 * (- 7 / 2 + rr * (rr * (1 / 2))) \<or> 21743271936 / 7992538801 \<le> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) \<or> - 7 / 2 + rr * (rr * (1 / 2)) \<le> 0"
      using leq_right_divide_mul_pos by blast (* 8 ms *)
    have ff3: "\<And>r ra. ra < exp r \<or> \<not> lgen True ra (exp r)"
      using lgen_less_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen True ra ((1 + r / 3 + 1 / 2 * (r / 3)\<^sup>2 + 1 / 6 * (r / 3) ^ 3 + 1 / 24 * (r / 3) ^ 4 + 1 / 120 * (r / 3) ^ 5) ^ 3) \<or> lgen True ra (exp r)"
      using exp_lower_taylor_5_cubed by auto (* failed *)
    then have "\<And>r ra. ra < exp r \<or> \<not> lgen True ra ((1 + r / 3 + 1 / 2 * (r / 3)\<^sup>2 + 1 / 6 * (r / 3) ^ 3 + 1 / 24 * (r / 3) ^ 4 + 1 / 120 * (r / 3) ^ 5) ^ 3)"
      using ff3 by blast (* 4 ms *)
    then have "\<And>r ra. (ra::real) < exp r \<or> 1 + r * (1 + r * (1 / 2 + r * (1 / 6 + r * (1 / 24 + r * (1 / 120 + r * (121 / 87480 + r * (17 / 87480 + r * (49 / 2099520 + r * (409 / 170061120 + r * (361 / 1700611200 + r * (1 / 62985600 + r * (181 / 183666009600 + r * (1 / 20407334400 + r * (1 / 550998028800 + r * (1 / 24794911296000))))))))))))))) \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff4: "(1::real) < exp 1 \<or> (1::real) + 1 * (1 + 1 * (1 / 2 + 1 * (1 / 6 + 1 * (1 / 24 + 1 * (1 / 120 + 1 * (121 / 87480 + 1 * (17 / 87480 + 1 * (49 / 2099520 + 1 * (409 / 170061120 + 1 * (361 / 1700611200 + 1 * (1 / 62985600 + 1 * (181 / 183666009600 + 1 * (1 / 20407334400 + 1 * (1 / 550998028800 + 1 * (1 / 24794911296000))))))))))))))) \<le> 1"
      by blast (* 8 ms *)
    have ff5: "\<And>r ra. \<not> lgen False (exp ra) r \<or> exp ra \<le> r"
      using lgen_le_neg by blast (* 0.0 ms *)
    have "\<And>r ra. 3 < ra \<or> \<not> lgen False (21743271936 / (- (ra ^ 3) + 12 * ra\<^sup>2 - 96 * ra + 384) ^ 4) r \<or> lgen False (exp ra) r"
      using exp_upper_bound_case_5 by auto (* failed *)
    then have "\<And>r ra. 3 < ra \<or> \<not> lgen False (21743271936 / (- (ra ^ 3) + 12 * ra\<^sup>2 - 96 * ra + 384) ^ 4) r \<or> exp ra \<le> r"
      using ff5 by blast (* 4 ms *)
    then have ff6: "\<And>r ra. 3 < (ra::real) \<or> r < 21743271936 / (21743271936 + ra * (- 21743271936 + ra * (10871635968 + ra * (- 3623878656 + ra * (891813888 + ra * (- 169869312 + ra * (25657344 + ra * (- 3096576 + ra * (297216 + ra * (- 22272 + ra * (1248 + ra * (- 48 + ra)))))))))))) \<or> exp ra \<le> r"
      by mt_arith_rule (* failed *)
    then have ff7: "3 < (1::real) \<or> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < 21743271936 / (21743271936 + 1 * (- 21743271936 + 1 * (10871635968 + 1 * (- 3623878656 + 1 * (891813888 + 1 * (- 169869312 + 1 * (25657344 + 1 * (- 3096576 + 1 * (297216 + 1 * (- 22272 + 1 * (1248 + 1 * (- 48 + 1)))))))))))) \<or> exp 1 \<le> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2)))"
      by blast (* 4 ms *)
    have ff8: "ln rr < - 1 * rra \<or> - 1 \<le> ln rr / rra \<or> rra \<le> 0"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff9: "(rra + exp 1) * (1 + rr * 2) < 5 / 2 + rr * (- 2 + rr * (- 1 / 2)) + exp 1 * (- 5 / 2 + rr * (2 + rr * (1 / 2))) \<or> 1 + rr * 2 \<le> 0 \<or> (5 / 2 + rr * (- 2 + rr * (- 1 / 2)) + exp 1 * (- 5 / 2 + rr * (2 + rr * (1 / 2)))) / (1 + rr * 2) \<le> rra + exp 1"
      using leq_left_divide_mul_pos by blast (* 4 ms *)
    have ff10: "rra + exp 1 < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) * (- 1 + exp 1) \<or> - (1::real) + exp 1 \<le> 0 \<or> (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<le> (rra + exp 1) / (- 1 + exp 1)"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff11: "rra + ln rr < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) * rra \<or> (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<le> (rra + ln rr) / rra \<or> rra \<le> 0"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff12: "exp (ln rr / rra) * rra < (- 1 + ln rr) * exp 1 \<or> - 1 + ln rr \<le> exp (ln rr / rra) * rra / exp 1 \<or> exp (1::real) \<le> 0"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff13: "\<And>r ra. \<not> lgen False ra (exp r) \<or> ra \<le> exp r"
      using lgen_le_neg by blast (* 0.0 ms *)
    have "\<And>r ra. ra < - 1 \<or> \<not> lgen False r (1 + ra) \<or> lgen False r (exp ra)"
      using exp_lower_taylor_1 by auto (* failed *)
    then have "\<And>r ra. ra < - 1 \<or> \<not> lgen False r (1 + ra) \<or> r \<le> exp ra"
      using ff13 by blast (* 4 ms *)
    then have "\<And>r ra. (1::real) + ra < r \<or> ra < - 1 \<or> r \<le> exp ra"
      by mt_arith_rule (* failed *)
    then have ff14: "ln rr / rra < - 1 \<or> 1 + ln rr / rra < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<or> (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<le> exp (ln rr / rra)"
      by blast (* 0.0 ms *)
    have ff15: "\<And>r ra. \<not> lgen False ra (exp r) \<or> ra \<le> exp r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. 0 < ra \<or> lgen False ra (exp r)"
      using exp_positive by auto (* failed *)
    then have ff16: "\<And>r ra. (0::real) < ra \<or> ra \<le> exp r"
      using ff15 by metis (* 4 ms *)
    then have ff17: "0 < ln rr * exp 1 \<or> ln rr * exp 1 \<le> exp 1"
      by blast (* 0.0 ms *)
    have ff18: "0 < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<or> (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<le> exp (ln rr / rra)"
      using ff16 by blast (* 4 ms *)
    have ff19: "exp 1 + ln rr * (exp 1 * - 1) < 0 * (rra * - 1) \<or> 0 \<le> rra * - 1 \<or> (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<le> 0"
      using leq_right_divide_mul_neg by blast (* 8 ms *)
    have ff20: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf3 by blast (* 0.0 ms *)
    then have "\<And>r ra. \<not> lgen False (1 / 2 * (ra + 5) * (ra - 1) / (2 * ra + 1)) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff20 by blast (* 4 ms *)
    then have ff21: "\<And>r ra. (ra::real) < (- 5 / 2 + r * (2 + r * (1 / 2))) / (1 + r * 2) \<or> r \<le> 0 \<or> ln r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff22: "(rra + exp 1) / (- 1 + exp 1) < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<or> ln rr \<le> (rra + exp 1) / (- 1 + exp 1) \<or> rr \<le> 0"
      by blast (* 4 ms *)
    have ff23: "1 * (1 + rr * 2) < - 5 / 2 + rr * (2 + rr * (1 / 2)) \<or> 1 + rr * 2 \<le> 0 \<or> (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<le> 1"
      using leq_left_divide_mul_pos by blast (* 4 ms *)
    have ff24: "1 < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<or> ln rr \<le> 1 \<or> rr \<le> 0"
      using ff21 by auto (* 4 ms *)
    have ff25: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by auto (* 4 ms *)
    have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf1 by blast (* 0.0 ms *)
    then have "\<And>r ra. \<not> lgen False (ra - 1) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff25 by auto (* 4 ms *)
    then have ff26: "\<And>r ra. (ra::real) < - 1 + r \<or> r \<le> 0 \<or> ln r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff27: "1 < - 1 + rr \<or> ln rr \<le> 1 \<or> rr \<le> 0"
      by blast (* 4 ms *)
    have ff28: "\<And>r ra. \<not> lgen False ra (ln r) \<or> ra \<le> ln r"
      using lgen_le_neg by auto (* 4 ms *)
    have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> lgen False ra (ln r)"
      using ln_lower_bound_cf1 by blast (* 4 ms *)
    then have "\<And>r ra. \<not> lgen False ra ((r - 1) / r) \<or> r \<le> 0 \<or> ra \<le> ln r"
      using ff28 by metis (* 8 ms *)
    then have "\<And>r ra. (- (1::real) + ra) / ra < r \<or> ra \<le> 0 \<or> r \<le> ln ra"
      by mt_arith_rule (* failed *)
    then have ff29: "(- 1 + rr) / rr < rra * - 1 \<or> rra * - 1 \<le> ln rr \<or> rr \<le> 0"
      by blast (* 4 ms *)
    have ff30: "- 1 + rra + rr < 21743271936 / 7992538801 * (- 2 + rr) \<or> 21743271936 / 7992538801 \<le> (- 1 + rra + rr) / (- 2 + rr) \<or> - 2 + rr \<le> 0"
      using leq_right_divide_mul_pos by blast (* 4 ms *)
    have ff31: "3 < (1::real) \<or> (- 1 + rra + rr) / (- 2 + rr) < 21743271936 / (21743271936 + 1 * (- 21743271936 + 1 * (10871635968 + 1 * (- 3623878656 + 1 * (891813888 + 1 * (- 169869312 + 1 * (25657344 + 1 * (- 3096576 + 1 * (297216 + 1 * (- 22272 + 1 * (1248 + 1 * (- 48 + 1)))))))))))) \<or> exp 1 \<le> (- 1 + rra + rr) / (- 2 + rr)"
      using ff6 by blast (* 8 ms *)
    have ff32: "rra + exp 1 < (- 1 + rr) * (- 1 + exp 1) \<or> - (1::real) + exp 1 \<le> 0 \<or> - 1 + rr \<le> (rra + exp 1) / (- 1 + exp 1)"
      using leq_right_divide_mul_pos by blast (* 8 ms *)
    have ff33: "(rra + exp 1) / (- 1 + exp 1) < - 1 + rr \<or> ln rr \<le> (rra + exp 1) / (- 1 + exp 1) \<or> rr \<le> 0"
      using ff26 by blast (* 4 ms *)
    have ff34: "1 * (1 + rr * (12 + rr * (18 + rr * 4))) < - 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4)))) \<or> 1 + rr * (12 + rr * (18 + rr * 4)) \<le> 0 \<or> (- 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4))))) / (1 + rr * (12 + rr * (18 + rr * 4))) \<le> 1"
      using leq_left_divide_mul_pos by blast (* 8 ms *)
    have ff35: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by auto (* 0.0 ms *)
    have "\<And>r ra. \<not> lgen False (1 / 12 * (3 * ra ^ 3 + 131 * ra\<^sup>2 + 239 * ra + 47) * (ra - 1) / (4 * ra ^ 3 + 18 * ra\<^sup>2 + 12 * ra + 1)) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf7 by auto (* failed *)
    then have "\<And>r ra. \<not> lgen False (1 / 12 * (3 * ra ^ 3 + 131 * ra\<^sup>2 + 239 * ra + 47) * (ra - 1) / (4 * ra ^ 3 + 18 * ra\<^sup>2 + 12 * ra + 1)) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff35 by blast (* 4 ms *)
    then have "\<And>r ra. (ra::real) < (- 47 / 12 + r * (- 16 + r * (9 + r * (32 / 3 + r * (1 / 4))))) / (1 + r * (12 + r * (18 + r * 4))) \<or> r \<le> 0 \<or> ln r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff36: "1 < (- 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4))))) / (1 + rr * (12 + rr * (18 + rr * 4))) \<or> ln rr \<le> 1 \<or> rr \<le> 0"
      by blast (* 4 ms *)
    have ff37: "1 * (1 + rr * (6 + rr * 3)) < - 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3))) \<or> 1 + rr * (6 + rr * 3) \<le> 0 \<or> (- 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3)))) / (1 + rr * (6 + rr * 3)) \<le> 1"
      using leq_left_divide_mul_pos by blast (* 8 ms *)
    have ff38: "\<And>r ra. \<not> lgen False (ln ra) r \<or> ln ra \<le> r"
      using lgen_le_neg by auto (* 4 ms *)
    have "\<And>r ra. \<not> lgen False (1 / 3 * (ra\<^sup>2 + 19 * ra + 10) * (ra - 1) / (3 * ra\<^sup>2 + 6 * ra + 1)) r \<or> ra \<le> 0 \<or> lgen False (ln ra) r"
      using ln_upper_bound_cf5 by auto (* failed *)
    then have "\<And>r ra. \<not> lgen False (1 / 3 * (ra\<^sup>2 + 19 * ra + 10) * (ra - 1) / (3 * ra\<^sup>2 + 6 * ra + 1)) r \<or> ra \<le> 0 \<or> ln ra \<le> r"
      using ff38 by blast (* 4 ms *)
    then have "\<And>r ra. (ra::real) < (- 10 / 3 + r * (- 3 + r * (6 + r * (1 / 3)))) / (1 + r * (6 + r * 3)) \<or> r \<le> 0 \<or> ln r \<le> ra"
      by mt_arith_rule (* failed *)
    then have ff39: "1 < (- 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3)))) / (1 + rr * (6 + rr * 3)) \<or> ln rr \<le> 1 \<or> rr \<le> 0"
      by blast (* 0.0 ms *)
    have "\<not> rr * (- 1 + rra * - 1) \<le> - 1 \<or> \<not> - 1 < rr * (- 1 + rra * - 1)"
      by simp (* 4 ms *)
    moreover
    { assume "\<not> - 1 < rr * (- 1 + rra * - 1)"
      then have "\<not> - 1 + rr < rra * - 1 * rr"
        by mt_arith_rule (* 8 ms *)
      then have "0 < rr \<longrightarrow> \<not> - 1 + rr < rra * - 1 * rr \<and> \<not> rr \<le> 0"
        by auto (* 0.0 ms *)
      moreover
      { assume "\<not> - 1 + rr < rra * - 1 * rr \<and> \<not> rr \<le> 0"
        then have "\<not> (- 1 + rr) / rr < rra * - 1"
          using ff1 by auto (* 8 ms *)
        then have "7 / 2 < rr * (rr * (1 / 2)) \<longrightarrow> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> rr * (rr * (1 / 2)) \<le> 7 / 2"
          by simp (* 4 ms *)
        moreover
        { assume "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> rr * (rr * (1 / 2)) \<le> 7 / 2"
          then have "\<not> rr * (rr * (1 / 2)) \<le> 7 / 2 \<and> \<not> rr * (- 2 + rra * - 2 + rr * (13750733135 / 15985077602)) \<le> 112240209547 / 15985077602 + rra \<or> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> 112240209547 / 15985077602 + rra < rr * (- 2 + rra * - 2 + rr * (13750733135 / 15985077602)) \<and> \<not> rr * (rr * (1 / 2)) \<le> 7 / 2"
            by auto (* 152 ms *)
          moreover
          { assume "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> 112240209547 / 15985077602 + rra < rr * (- 2 + rra * - 2 + rr * (13750733135 / 15985077602)) \<and> \<not> rr * (rr * (1 / 2)) \<le> 7 / 2"
            then have "\<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < 21743271936 / 7992538801 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> - 7 / 2 + rr * (rr * (1 / 2)) \<le> 0"
              by mt_arith_rule (* 728 ms *)
            then have "\<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < 21743271936 / 7992538801 \<and> \<not> (- 1 + rr) / rr < rra * - 1"
              using ff2 by simp (* 108 ms *)
            then have "\<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < 21743271936 / 7992538801 \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (1::real) + 1 * (1 + 1 * (1 / 2 + 1 * (1 / 6 + 1 * (1 / 24 + 1 * (1 / 120 + 1 * (121 / 87480 + 1 * (17 / 87480 + 1 * (49 / 2099520 + 1 * (409 / 170061120 + 1 * (361 / 1700611200 + 1 * (1 / 62985600 + 1 * (181 / 183666009600 + 1 * (1 / 20407334400 + 1 * (1 / 550998028800 + 1 * (1 / 24794911296000))))))))))))))) \<le> 1"
              by mt_arith_rule (* 288 ms *)
            then have "\<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < 21743271936 / 7992538801 \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1"
              using ff4 by fastforce (* 280 ms *)
            then have "\<not> 3 < (1::real) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < 21743271936 / (21743271936 + 1 * (- 21743271936 + 1 * (10871635968 + 1 * (- 3623878656 + 1 * (891813888 + 1 * (- 169869312 + 1 * (25657344 + 1 * (- 3096576 + 1 * (297216 + 1 * (- 22272 + 1 * (1248 + 1 * (- 48 + 1)))))))))))) \<and> \<not> exp (1::real) \<le> 1"
              by mt_arith_rule (* 100 ms *)
            then have "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < exp 1 \<and> \<not> exp (1::real) \<le> 1"
              using ff7 by simp (* 112 ms *)
            then have "7 / 2 < rr * (rr * (1 / 2)) \<longrightarrow> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < exp 1 \<and> \<not> rr * (rr * (1 / 2)) \<le> 7 / 2 \<and> \<not> exp (1::real) \<le> 1"
              by auto (* 12 ms *)
            moreover
            { assume "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2))) / (- 7 / 2 + rr * (rr * (1 / 2))) < exp 1 \<and> \<not> rr * (rr * (1 / 2)) \<le> 7 / 2 \<and> \<not> exp (1::real) \<le> 1"
              then have "\<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1"
                by mt_arith_rule (* 148 ms *)
              then have "0 < rr \<longrightarrow> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                by fastforce (* 4 ms *)
              moreover
              { assume "\<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                then have "\<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> ln rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1"
                  using ff29 by auto (* 8 ms *)
                then have "\<not> ln rr < - 1 * rra \<and> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> exp (1::real) \<le> 1"
                  by mt_arith_rule (* 36 ms *)
                then have "0 < rra \<longrightarrow> \<not> ln rr < - 1 * rra \<and> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rra \<le> 0"
                  by auto (* 4 ms *)
                moreover
                { assume "\<not> ln rr < - 1 * rra \<and> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rra \<le> 0"
                  then have "\<not> ln rr / rra < - 1 \<and> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> exp (1::real) \<le> 1"
                    using ff8 by auto (* 8 ms *)
                  then have "- 1 / 2 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> - 1 / 2"
                    by simp (* 8 ms *)
                  moreover
                  { assume "\<not> ln rr / rra < - 1 \<and> \<not> - 5 / 2 + rra + rr * (2 + rra * 2 + rr * (1 / 2)) < exp 1 * (- 7 / 2 + rr * (rr * (1 / 2))) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> - 1 / 2"
                    then have "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) * (1 + rr * 2) < 5 / 2 + rr * (- 2 + rr * (- 1 / 2)) + exp 1 * (- 5 / 2 + rr * (2 + rr * (1 / 2))) \<and> \<not> 1 + rr * 2 \<le> 0 \<and> \<not> exp (1::real) \<le> 1"
                      by mt_arith_rule (* 256 ms *)
                    then have "\<not> ln rr / rra < - 1 \<and> \<not> rra + exp 1 < (5 / 2 + rr * (- 2 + rr * (- 1 / 2)) + exp 1 * (- 5 / 2 + rr * (2 + rr * (1 / 2)))) / (1 + rr * 2) \<and> \<not> exp (1::real) \<le> 1"
                      using ff9 by simp (* 64 ms *)
                    then have "\<not> ln rr / rra < - 1 \<and> \<not> rra + exp 1 < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) * (- 1 + exp 1) \<and> \<not> - (1::real) + exp 1 \<le> 0 \<and> \<not> exp (1::real) \<le> 1"
                      by mt_arith_rule (* 568 ms *)
                    then have "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<and> \<not> exp (1::real) \<le> 1"
                      using ff10 by auto (* 32 ms *)
                    then have "0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                      by auto (* 4 ms *)
                    moreover
                    { assume "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                      then have "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                        using ff22 by simp (* 12 ms *) }
                    ultimately have "0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                      by metis (* 12 ms *) }
                  moreover
                  { assume "\<not> - 1 / 2 < rr"
                    then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
                      by sos (* 20 ms *) }
                  ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                    by metis (* 24 ms *) }
                ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                  by metis (* 32 ms *) }
              ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                by metis (* 56 ms *) }
            ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
              by metis (* 56 ms *) }
          moreover
          { assume "\<not> rr * (rr * (1 / 2)) \<le> 7 / 2 \<and> \<not> rr * (- 2 + rra * - 2 + rr * (13750733135 / 15985077602)) \<le> 112240209547 / 15985077602 + rra"
            then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<or> \<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
              by sos (* 316 ms *) }
          ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
            by metis (* 192 ms *) }
        ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
          by metis (* 144 ms *) }
      ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
        by metis (* 116 ms *) }
    moreover
    { assume "\<not> rr * (- 1 + rra * - 1) \<le> - 1"
      then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<or> \<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
        sorry (*by sos*) (* > 5.0 s, timed out *) }
    ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
      by metis (* 92 ms *)
    moreover
    { assume "\<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr"
      then have "\<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> \<not> rr * (- 1 + rra * - 1) \<le> - 1 \<or> \<not> - 1 < rr * (- 1 + rra * - 1) \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr"
        by simp (* 20 ms *)
      moreover
      { assume "\<not> - 1 < rr * (- 1 + rra * - 1) \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr"
        then have "\<not> - 1 + rr < rra * - 1 * rr \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr"
          by mt_arith_rule (* 124 ms *)
        then have "0 < rr \<longrightarrow> \<not> - 1 + rr < rra * - 1 * rr \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> \<not> rr \<le> 0"
          by force (* 4 ms *)
        moreover
        { assume "\<not> - 1 + rr < rra * - 1 * rr \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> \<not> rr \<le> 0"
          then have "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr"
            using ff1 by auto (* 16 ms *)
          then have "\<not> 2 < rr \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<or> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> \<not> rr \<le> 2"
            by force (* 8 ms *)
          moreover
          { assume "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> \<not> rr \<le> 2"
            then have "\<not> - 1 + rra + rr < 21743271936 / 7992538801 * (- 2 + rr) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> - 2 + rr \<le> 0"
              by mt_arith_rule (* 116 ms *)
            then have "\<not> (- 1 + rra + rr) / (- 2 + rr) < 21743271936 / 7992538801 \<and> \<not> (- 1 + rr) / rr < rra * - 1"
              using ff30 by simp (* 68 ms *)
            then have "\<not> (- 1 + rra + rr) / (- 2 + rr) < 21743271936 / 7992538801 \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (1::real) + 1 * (1 + 1 * (1 / 2 + 1 * (1 / 6 + 1 * (1 / 24 + 1 * (1 / 120 + 1 * (121 / 87480 + 1 * (17 / 87480 + 1 * (49 / 2099520 + 1 * (409 / 170061120 + 1 * (361 / 1700611200 + 1 * (1 / 62985600 + 1 * (181 / 183666009600 + 1 * (1 / 20407334400 + 1 * (1 / 550998028800 + 1 * (1 / 24794911296000))))))))))))))) \<le> 1"
              by mt_arith_rule (* 208 ms *)
            then have "\<not> (- 1 + rra + rr) / (- 2 + rr) < 21743271936 / 7992538801 \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1"
              using ff4 by force (* 260 ms *)
            then have "\<not> 3 < (1::real) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 1 + rra + rr) / (- 2 + rr) < 21743271936 / (21743271936 + 1 * (- 21743271936 + 1 * (10871635968 + 1 * (- 3623878656 + 1 * (891813888 + 1 * (- 169869312 + 1 * (25657344 + 1 * (- 3096576 + 1 * (297216 + 1 * (- 22272 + 1 * (1248 + 1 * (- 48 + 1)))))))))))) \<and> \<not> exp (1::real) \<le> 1"
              by mt_arith_rule (* 48 ms *)
            then have "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 1 + rra + rr) / (- 2 + rr) < exp 1 \<and> \<not> exp (1::real) \<le> 1"
              using ff31 by fastforce (* 72 ms *)
            then have "2 < rr \<longrightarrow> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 1 + rra + rr) / (- 2 + rr) < exp 1 \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 2"
              by simp (* 4 ms *)
            moreover
            { assume "\<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> (- 1 + rra + rr) / (- 2 + rr) < exp 1 \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 2"
              then have "\<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1"
                by mt_arith_rule (* 24 ms *)
              then have "0 < rr \<longrightarrow> \<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                by auto (* 4 ms *)
              moreover
              { assume "\<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> (- 1 + rr) / rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                then have "\<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> ln rr < rra * - 1 \<and> \<not> exp (1::real) \<le> 1"
                  using ff29 by auto (* 8 ms *)
                then have "\<not> ln rr < - 1 * rra \<and> \<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> exp (1::real) \<le> 1"
                  by mt_arith_rule (* 0.0 ms *)
                then have "0 < rra \<longrightarrow> \<not> ln rr < - 1 * rra \<and> \<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rra \<le> 0"
                  by auto (* 4 ms *)
                moreover
                { assume "\<not> ln rr < - 1 * rra \<and> \<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rra \<le> 0"
                  then have "\<not> ln rr / rra < - 1 \<and> \<not> - 1 + rra + rr < exp 1 * (- 2 + rr) \<and> \<not> exp (1::real) \<le> 1"
                    using ff8 by simp (* 4 ms *)
                  then have "\<not> ln rr / rra < - 1 \<and> \<not> rra + exp 1 < (- 1 + rr) * (- 1 + exp 1) \<and> \<not> - (1::real) + exp 1 \<le> 0 \<and> \<not> exp (1::real) \<le> 1"
                    by mt_arith_rule (* 44 ms *)
                  then have "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < - 1 + rr \<and> \<not> exp (1::real) \<le> 1"
                    using ff32 by auto (* 12 ms *)
                  then have "0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < - 1 + rr \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                    by auto (* 4 ms *)
                  moreover
                  { assume "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < - 1 + rr \<and> \<not> exp (1::real) \<le> 1 \<and> \<not> rr \<le> 0"
                    then have "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                      using ff33 by auto (* 8 ms *) }
                  ultimately have "0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                    by metis (* 8 ms *) }
                ultimately have "0 < rra \<and> 0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                  by metis (* 16 ms *) }
              ultimately have "0 < rra \<and> 0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
                by metis (* 16 ms *) }
            ultimately have "2 < rr \<and> 0 < rra \<and> 0 < rr \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
              by metis (* 16 ms *) }
          moreover
          { assume "\<not> 2 < rr \<and> \<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr"
            then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
              by sos (* 48 ms *) }
          ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
            by metis (* 56 ms *) }
        ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
          by metis (* 68 ms *) }
      moreover
      { assume "\<not> 35494005071 / 13750733135 + rra * (7992538801 / 13750733135) < rr \<and> \<not> rr * (- 1 + rra * - 1) \<le> - 1"
        then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
          sorry (*by sos*) (* > 5.0 s, timed out *) }
      ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
        by metis (* 100 ms *) }
    ultimately have "1 < rr \<and> 2 < rr \<and> 7 / 2 < rr * (rr * (1 / 2)) \<and> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> 0 < rra \<and> 0 < rr \<and> rr < 4 \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
      by metis (* 100 ms *)
    moreover
    { assume "\<not> ln rr / rra < - 1 \<and> \<not> (rra + exp 1) / (- 1 + exp 1) < ln rr \<and> \<not> exp (1::real) \<le> 1"
      then have "\<not> ln rr / rra < - 1 \<and> \<not> rra + exp 1 < ln rr * (- 1 + exp 1)"
        by mt_arith_rule (* 4 ms *)
      then have "\<not> ln rr / rra < - 1 \<and> \<not> rra + exp 1 < ln rr * (- 1 + exp 1) \<and> rra \<noteq> 0 \<or> rra = 0"
        by auto (* 0.0 ms *)
      moreover
      { assume "\<not> ln rr / rra < - 1 \<and> \<not> rra + exp 1 < ln rr * (- 1 + exp 1) \<and> rra \<noteq> 0"
        then have "\<not> ln rr / rra < - 1 \<and> \<not> rra + ln rr < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) * rra"
          by mt_arith_rule (* 24 ms *)
        then have "0 < rra \<longrightarrow> \<not> ln rr / rra < - 1 \<and> \<not> rra + ln rr < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) * rra \<and> \<not> rra \<le> 0"
          by fastforce (* 4 ms *)
        moreover
        { assume "\<not> ln rr / rra < - 1 \<and> \<not> rra + ln rr < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) * rra \<and> \<not> rra \<le> 0"
          then have "\<not> ln rr / rra < - 1 \<and> \<not> (rra + ln rr) / rra < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
            using ff11 by fastforce (* 52 ms *)
          then have "rra = 0 \<or> \<not> ln rr / rra < - 1 \<and> \<not> (rra + ln rr) / rra < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> rra \<noteq> 0"
            by fastforce (* 0.0 ms *)
          moreover
          { assume "\<not> ln rr / rra < - 1 \<and> \<not> (rra + ln rr) / rra < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> rra \<noteq> 0"
            then have "\<not> ln rr / rra < - 1 \<and> \<not> 1 + ln rr / rra < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
              by mt_arith_rule (* 8 ms *)
            then have "\<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
              using ff14 by simp (* 8 ms *) }
          ultimately have "exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<longrightarrow> rra = 0"
            by metis (* 16 ms *) }
        ultimately have "exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> 0 < rra \<longrightarrow> rra = 0"
          by metis (* 40 ms *) }
      ultimately have "exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> 0 < rra \<longrightarrow> rra = 0"
        by metis (* 16 ms *)
      moreover
      { assume "rra = 0"
        then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 1 < rr"
          by sos (* 16 ms *) }
      ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 1 < rr \<or> \<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
        by metis (* 20 ms *) }
    moreover
    { assume "\<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4))))"
      then have "\<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> \<not> - 1 < rr * (12 + rr * (18 + rr * 4)) \<or> \<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> \<not> rr * (12 + rr * (18 + rr * 4)) \<le> - 1"
        by simp (* 16 ms *)
      moreover
      { assume "\<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> \<not> rr * (12 + rr * (18 + rr * 4)) \<le> - 1"
        then have "\<not> 1 * (1 + rr * (12 + rr * (18 + rr * 4))) < - 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4)))) \<and> \<not> 1 + rr * (12 + rr * (18 + rr * 4)) \<le> 0"
          by mt_arith_rule (* 80 ms *)
        then have "\<not> 1 < (- 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4))))) / (1 + rr * (12 + rr * (18 + rr * 4)))"
          using ff34 by auto (* 96 ms *)
        then have "0 < rr \<longrightarrow> \<not> 1 < (- 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4))))) / (1 + rr * (12 + rr * (18 + rr * 4))) \<and> \<not> rr \<le> 0"
          by simp (* 4 ms *)
        moreover
        { assume "\<not> 1 < (- 47 / 12 + rr * (- 16 + rr * (9 + rr * (32 / 3 + rr * (1 / 4))))) / (1 + rr * (12 + rr * (18 + rr * 4))) \<and> \<not> rr \<le> 0"
          then have "\<not> 1 < ln rr"
            using ff36 by fastforce (* 8 ms *) }
        ultimately have "\<not> 0 < rr \<or> \<not> 1 < ln rr"
          by metis (* 8 ms *) }
      moreover
      { assume "\<not> 59 / 12 < rr * (- 28 + rr * (- 9 + rr * (20 / 3 + rr * (1 / 4)))) \<and> \<not> - 1 < rr * (12 + rr * (18 + rr * 4))"
        then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
          by sos (* > 5.0 s, timed out *) }
      ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < ln rr \<or> \<not> 1 < rr"
        by metis (* 28 ms *) }
    ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < ln rr \<or> \<not> 1 < rr \<or> \<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
      by metis (* 48 ms *)
    moreover
    { assume "\<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3)))"
      then have "\<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> \<not> - 1 < rr * (6 + rr * 3) \<or> \<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> \<not> rr * (6 + rr * 3) \<le> - 1"
        by auto (* 8 ms *)
      moreover
      { assume "\<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> \<not> rr * (6 + rr * 3) \<le> - 1"
        then have "\<not> 1 * (1 + rr * (6 + rr * 3)) < - 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3))) \<and> \<not> 1 + rr * (6 + rr * 3) \<le> 0"
          by mt_arith_rule (* 40 ms *)
        then have "\<not> 1 < (- 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3)))) / (1 + rr * (6 + rr * 3))"
          using ff37 by simp (* 48 ms *)
        then have "0 < rr \<longrightarrow> \<not> 1 < (- 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3)))) / (1 + rr * (6 + rr * 3)) \<and> \<not> rr \<le> 0"
          by simp (* 4 ms *)
        moreover
        { assume "\<not> 1 < (- 10 / 3 + rr * (- 3 + rr * (6 + rr * (1 / 3)))) / (1 + rr * (6 + rr * 3)) \<and> \<not> rr \<le> 0"
          then have "\<not> 1 < ln rr"
            using ff39 by fastforce (* 20 ms *) }
        ultimately have "\<not> 0 < rr \<or> \<not> 1 < ln rr"
          by metis (* 12 ms *) }
      moreover
      { assume "\<not> 13 / 3 < rr * (- 9 + rr * (3 + rr * (1 / 3))) \<and> \<not> - 1 < rr * (6 + rr * 3)"
        then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
          by sos (* 32 ms *) }
      ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < ln rr \<or> \<not> 1 < rr"
        by metis (* 20 ms *) }
    ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<or> \<not> 2 < rr \<or> \<not> 1 < ln rr \<or> \<not> 1 < rr \<or> \<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
      by metis (* 20 ms *)
    moreover
    { assume "\<not> 7 / 2 < rr * (rr * (1 / 2))"
      then have "\<not> 7 / 2 < rr * (rr * (1 / 2)) \<and> \<not> - 1 / 2 < rr \<or> \<not> 7 / 2 < rr * (rr * (1 / 2)) \<and> \<not> rr \<le> - 1 / 2"
        by auto (* 12 ms *)
      moreover
      { assume "\<not> 7 / 2 < rr * (rr * (1 / 2)) \<and> \<not> rr \<le> - 1 / 2"
        then have "\<not> 1 * (1 + rr * 2) < - 5 / 2 + rr * (2 + rr * (1 / 2)) \<and> \<not> 1 + rr * 2 \<le> 0"
          by mt_arith_rule (* 16 ms *)
        then have "\<not> 1 < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2)"
          using ff23 by simp (* 28 ms *)
        then have "0 < rr \<longrightarrow> \<not> 1 < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<and> \<not> rr \<le> 0"
          by auto (* 4 ms *)
        moreover
        { assume "\<not> 1 < (- 5 / 2 + rr * (2 + rr * (1 / 2))) / (1 + rr * 2) \<and> \<not> rr \<le> 0"
          then have "\<not> 1 < ln rr"
            using ff24 by simp (* 8 ms *) }
        ultimately have "\<not> 0 < rr \<or> \<not> 1 < ln rr"
          by metis (* 8 ms *) }
      moreover
      { assume "\<not> 7 / 2 < rr * (rr * (1 / 2)) \<and> \<not> - 1 / 2 < rr"
        then have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 2 < rr \<or> \<not> 1 < rr"
          by sos (* 20 ms *) }
      ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 2 < rr \<or> \<not> 1 < ln rr \<or> \<not> 1 < rr"
        by metis (* 12 ms *) }
    ultimately have "\<not> rr < 4 \<or> \<not> 0 < rr \<or> \<not> 0 < rra \<or> \<not> 2 < rr \<or> \<not> 1 < ln rr \<or> \<not> 1 < rr \<or> \<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 1 < rr"
      then have "0 < rr \<longrightarrow> \<not> 1 < rr \<and> \<not> rr \<le> 0"
        by auto (* 0.0 ms *)
      moreover
      { assume "\<not> 1 < rr \<and> \<not> rr \<le> 0"
        then have "\<not> 0 < ln rr * exp 1"
          by mt_arith_rule (* 8 ms *)
        then have "\<not> exp 1 < ln rr * exp 1"
          using ff17 by simp (* 8 ms *) }
      ultimately have "\<not> 0 < rr \<or> \<not> exp 1 < ln rr * exp 1"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> 2 < rr"
      then have "\<not> 1 < - 1 + rr"
        by mt_arith_rule (* 4 ms *)
      then have "0 < rr \<longrightarrow> \<not> 1 < - 1 + rr \<and> \<not> rr \<le> 0"
        by fastforce (* 0.0 ms *)
      moreover
      { assume "\<not> 1 < - 1 + rr \<and> \<not> rr \<le> 0"
        then have "\<not> 1 < ln rr"
          using ff27 by auto (* 4 ms *) }
      ultimately have "\<not> 0 < rr \<or> \<not> 1 < ln rr"
        by metis (* 4 ms *) }
    moreover
    { assume "\<not> rr < 4"
      then have "\<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
        by metis (* 4 ms *) }
    ultimately have "exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> exp 1 < ln rr * exp 1 \<and> 1 < ln rr \<and> 0 < rra \<and> 0 < rr \<longrightarrow> \<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 1 < ln rr"
      then have "\<not> exp 1 < ln rr * exp 1"
        by mt_arith_rule (* 4 ms *) }
    moreover
    { assume "\<not> 0 < rr"
      then have "\<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
        by metis (* 4 ms *) }
    ultimately have "exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> exp 1 < ln rr * exp 1 \<and> 0 < rra \<longrightarrow> \<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> exp 1 < ln rr * exp 1"
      then have "0 < rra \<longrightarrow> \<not> exp 1 < ln rr * exp 1 \<and> \<not> rra \<le> 0"
        by auto (* 0.0 ms *)
      moreover
      { assume "\<not> exp 1 < ln rr * exp 1 \<and> \<not> rra \<le> 0"
        then have "\<not> exp 1 + ln rr * (exp 1 * - 1) < 0 * (rra * - 1) \<and> \<not> 0 \<le> rra * - 1"
          by mt_arith_rule (* 4 ms *)
        then have "\<not> 0 < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
          using ff19 by force (* 8 ms *)
        then have "\<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
          using ff18 by auto (* 12 ms *) }
      ultimately have "\<not> 0 < rra \<or> \<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
        by metis (* 12 ms *) }
    ultimately have "exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> 0 < rra \<longrightarrow> \<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
      by metis (* 24 ms *)
    moreover
    { assume "\<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1)"
      then have "0 < rra \<longrightarrow> \<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> \<not> rra \<le> 0"
        by auto (* 0.0 ms *)
      moreover
      { assume "\<not> exp (ln rr / rra) < (exp 1 + ln rr * (exp 1 * - 1)) / (rra * - 1) \<and> \<not> rra \<le> 0"
        then have "\<not> exp 1 + ln rr * (exp 1 * - 1) < exp (ln rr / rra) * (rra * - 1)"
          by mt_arith_rule (* 12 ms *)
        then have "\<not> exp (ln rr / rra) * rra < (- 1 + ln rr) * exp 1 \<and> \<not> exp (1::real) \<le> 0"
          by mt_arith_rule (* 8 ms *)
        then have "\<not> exp (ln rr / rra) * rra / exp 1 < - 1 + ln rr"
          using ff12 by auto (* 8 ms *)
        then have "\<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr"
          by mt_arith_rule (* 8 ms *)
        then have "\<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
          by metis (* 4 ms *) }
      ultimately have "0 < rra \<longrightarrow> \<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
        by metis (* 12 ms *) }
    ultimately have "0 < rra \<longrightarrow> \<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
      by metis (* 12 ms *)
    moreover
    { assume "\<not> 0 < rra"
      then have "\<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
        by metis (* 4 ms *) }
    ultimately have "\<not> rr < 4 \<or> \<not> 1 + exp (ln rr / rra) * rra / exp 1 < ln rr \<or> \<not> 0 < rra \<or> \<not> 0 < rr"
      by metis (* 8 ms *) }
  then have "\<forall>r ra. \<not> (0::real) < r \<or> \<not> 0 < ra \<or> \<not> ra < 4 \<or> \<not> 1 + exp (ln ra / r) * r / exp 1 < ln ra"
    by meson (* 4 ms *)
  then show ?thesis
    by auto (* 8 ms *)
qed

end
  