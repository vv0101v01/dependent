# Module M3：`m3_pi_sigma_types`（依賴函數類型、依賴乘積類型、雙向判斷與類型導向 NbE）

本模組為獨立基礎模組（零跨模組依賴），涵蓋 **依賴函數類型（$\Pi$-Type）**、**依賴乘積類型（$\Sigma$-Type）**、**判斷（Judgment）**、**類型導向求值正規化（Type-Directed NbE）**、**依賴 Currying 伴隨同構** 與 **依賴 Skolem 選擇同構**（Trotta, Weinberger & de Paiva, 2024）。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **局部公理 M3.A1（Gentzen-Prawitz 局部邏輯消元與和諧性公理）**：
   - $\Pi$-局部可靠性（$\beta$-消元）與完備性（$\eta$-展開）：$(\lambda x:A. b)\ a \mapsto b[x := a]$，$f \equiv_\eta \lambda x:A. f\ x$。
   - $\Sigma$-局部可靠性（$\beta_1, \beta_2$-投影消元）與完備性（滿射配對 $\eta$-展開）：$\pi_1\langle a, b\rangle \mapsto a$，$\pi_2\langle a, b\rangle \mapsto b$，$p \equiv_\eta \langle \pi_1 p, \pi_2 p\rangle$。
   - $\mathbb{N}$ 與恆等類型 $\mathsf{Id}$ 之 $\iota$-消元：$\mathsf{natrec}(M, z, s, 0) \mapsto z$、$\mathsf{natrec}(M, z, s, \mathsf{S}(n)) \mapsto s(n, \mathsf{natrec}(M, z, s, n))$、$\mathsf{J}(A, a, M, r, a, \mathsf{refl}(a)) \mapsto r$。
   - 和類型 $\Sigma$-消元（case $\iota$-消元）：$\mathsf{case}(\mathsf{inl}(v), m, l, r) \mapsto l(v)$、$\mathsf{case}(\mathsf{inr}(v), m, l, r) \mapsto r(v)$；布林排序 $\mathsf{Bool}$ 具典範字面量 $\mathsf{true}, \mathsf{false}$ 與可判定轉換。
2. **定義 M3.D1（帶類型中性項之 Kripke 語意域 `Val` 與去函數化閉包 `Clos`）**：語法樹 `CoreTm` 使用 De Bruijn 索引，語意域 `Val` 使用 De Bruijn 層級與顯式環境閉包 `Clos{env, body}`；中性項 `VNeu(vty, Neutral)` 黏合攜帶其語意類型以驅動全函數 $\eta$-回讀。核心語法完整涵蓋 $\Pi, \Sigma, \mathbf{1}, \mathbb{N}, \mathsf{Id}, \|\cdot\|, \mathsf{Sum}, \mathsf{Empty}, \mathsf{Bool}$、多態宇宙變數 `CPolyUniv(v, o)` 與帶動機註記之配對 `CPair(a, b, m)`／帶類型註記之 `CRefl(t, x)`；語境反射 `JudgmentCtx::push_def` 將局部定義 `x : A := v` 之**值**注入語意環境，使後續引用於 NbE 中 zeta-展開。
3. **定理 M3.T1（類型導向 NbE 決定定義等價與證明無關性定理）**：回讀算子 $\mathsf{quote\_val}(d, \llbracket A \rrbracket, \llbracket t \rrbracket)$ 對任意良類型項產生唯一 $\beta\eta\iota$-正規形，並在單位類型 $\top$ 與截斷命題 $\|A\|_{-1}$ 上以 $O(1)$ 實現定義級證明無關性（Proof Irrelevance：$u \equiv v : \|A\|_{-1}$）。
4. **定理 M3.T2（雙向類型判斷合成與檢驗健全性定理）**：將判斷 $\Gamma \vdash t : A$ 分解為合成模式 $\Gamma \vdash t \Rightarrow A$ 與檢驗模式 $\Gamma \vdash t \Leftarrow A$，支援累積與非累積宇宙檢驗模式切換。
5. **定理 M3.T3（依賴 Currying 泛性質同構定理）**：對任意依賴族 $A, B(x), C(p)$，存在顯式互逆項轉換器 `dep_curry_term` 與 `dep_uncurry_term`，使得於開放上下文中恆成立定義等價：
   $$\Pi(p : \Sigma(x:A). B(x)). C(p) \;\simeq_{\beta\eta}\; \Pi(x:A). \Pi(y:B(x)). C(\langle x, y \rangle)$$
6. **定理 M3.T4（依賴 Skolem 化與類型論選擇公理同構定理）**：對任意依賴族 $A, B(x), C(x, y)$，`skolemize_term` 與 `deskolemize_term` 給出雙向互逆同構並於開放中性變數上滿足嚴格 $\beta\eta$ 往返恆等：
   $$\Pi(x:A). \Sigma(y:B(x)). C(x, y) \;\simeq_{\beta\eta}\; \Sigma\big(f : \Pi(x:A). B(x)\big). \Pi(x:A). C(x, f\ x)$$

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 去函數化閉包求值器 (`eval_tm`, `apply_val`, `fst_val`, `snd_val`, `natrec_val`, `j_elim_val`) | `domain_nbe.mbt` | 變數查找 $O(1)$ / 零語法平移求值 | 語意域採用 De Bruijn 層級陣列 `env[len-1-idx]`，徹底免除求值期語法樹平移 |
| 類型導向 $\beta\eta$ 正規形回讀與轉換決策器 (`quote_ty`, `quote_val`, `conv_ty`, `conv_val`) | `domain_nbe.mbt` | `Unit`/`Squash` 比較 $O(1)$ / 一般回讀 $O(\|nf\|)$ | 同時決定 $\Pi$-$\eta$、$\Sigma$-滿射配對 $\eta$、`Unit`-$\eta$、無煩 $\Downarrow/\Uparrow$ 往返與截斷命題證明無關性 |
| 雙向類型合成與檢驗核心 (`check_is_type`, `synth_term`, `check_term`) | `bidirectional_isomorphisms.mbt` | 語法導向單趟遍歷 + NbE 轉換測試 | 完整檢驗 $\Pi, \Sigma, \mathcal{U}_i, \mathsf{Prop}, \Downarrow_i/\Uparrow_i, \mathbb{N}, \mathsf{Id}, \|A\|_{-1}$ |
| 依賴 Currying / Uncurrying 雙向編譯器 (`dep_curry_term`, `dep_uncurry_term`) | `bidirectional_isomorphisms.mbt` | $O(\|t\|)$ | 精確重編碼 De Bruijn 索引並滿足 $\beta\eta$ 互逆恆等 |
| 依賴 Skolem 化與逆 Skolem 化見證拆分編譯器 (`skolemize_term`, `deskolemize_term`) | `bidirectional_isomorphisms.mbt` | $O(\|t\|)$ | 從全稱存在證明項拆分出純計算選擇函數 $\lambda x.\pi_1(h\ x)$ 與驗證憑證函數 $\lambda x.\pi_2(h\ x)$ |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │          dtt/m3_pi_sigma_types              │
             │              domain_nbe.mbt                 │
             │                    │                        │
             │                    ▼                        │
             │       bidirectional_isomorphisms.mbt        │
             └──────────────┬──────────────┬───────────────┘
                            │              │
          ┌─────────────────┘              └─────────────────┐
          ▼                                                  ▼
[ dtt/m5_fibration_kan ]                         [ dtt/m6_chu_galois_bridge ]
          │                                                  │
          └────────────────────────┬─────────────────────────┘
                                   ▼
                        [ dtt/m7_unified_kernel ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `domain_nbe.mbt`：將 De Bruijn 索引語法 `CoreTm` 求值至 De Bruijn 層級語意域 `Val`，執行 $\beta/\iota/\text{univ-beta}$ 局部消元，再透過 `quote_val` 執行類型導向 $\eta$-展開與證明無關收縮。
2. `bidirectional_isomorphisms.mbt`：維護反射上下文 `JudgmentCtx`，呼叫 `eval_tm` 與 `conv_ty`/`conv_val` 執行雙向類型推導與檢驗，並提供依賴 Currying 與依賴 Skolem 同構轉換。

### 輸出公共接口（Public API）
- **類型與錯誤**：`CoreTm`, `Clos`, `SpineElim`, `Neutral`, `Val`, `JudgmentCtx`, `TypeTheoryError`。
- **NbE 求值與回讀**：`shift_core`, `fresh_neutral_var`, `eval_clos`, `eval_clos2`, `apply_val`, `fst_val`, `snd_val`, `small_dec_val`, `natrec_val`, `j_elim_val`, `eval_tm`, `quote_ty`, `quote_val`, `conv_ty`, `conv_val`, `decode_nat_numeral`, `encode_nat_numeral`。
- **雙向判斷與泛同構**：`JudgmentCtx::empty`, `JudgmentCtx::depth`, `JudgmentCtx::push_var`, `JudgmentCtx::normalize`, `check_is_type`, `synth_term`, `check_term`, `dep_uncurried_type`, `dep_curried_type`, `dep_curry_term`, `dep_uncurry_term`, `skolem_source_type`, `skolem_target_type`, `skolemize_term`, `deskolemize_term`。
