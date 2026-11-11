# Module M4：`m4_curry_howard_prop`（柯里-霍華德對應、命題即類型、序列切消元與認證抹除）

本模組為獨立基礎模組（零跨模組依賴），涵蓋 **柯里-霍華德對應（Curry-Howard Correspondence）** 與 **命題即類型（Propositions-as-Types）** 之完整公理與演算法體系：一階依賴直覺主義謂詞邏輯與依賴證明演算雙向函子、截斷命題反射模態（Squash Modality）、Gentzen 序列演算 $\mathbf{LJD}$ 切消元（Cut-Elimination）與自然演繹 $\beta$-正規化交換圖、古典邏輯雙重否定 CPS 嵌入，以及認證證明抹除與計算見證提取（Sozeau et al., 2025）。

---

## 一、資料夾內已獲得之公理、定義、命題、引理與定理列表

1. **全域公理 M4.A1（柯里-霍華德雙向語法同構公理）**：一階依賴建構式謂詞邏輯公式空間 `PropFormula` 與依賴證明類型空間 `CHType` 之間存在嚴格互逆同構函子 $\llbracket - \rrbracket$ 與 $\llbracket - \rrbracket^{-1}$：
   $$\top \leftrightarrow \mathbf{1},\quad \bot \leftrightarrow \mathbf{0},\quad \phi \wedge \psi \leftrightarrow \phi \times \psi,\quad \phi \vee \psi \leftrightarrow \phi + \psi,\quad \phi \supset \psi \leftrightarrow \phi \to \psi,\quad \forall x:D.\phi \leftrightarrow \Pi(x:D).\phi,\quad \exists x:D.\phi \leftrightarrow \Sigma(x:D).\phi$$
2. **局部公理 M4.A2（Prawitz 迂迴消元與 Gentzen 切消元公理）**：自然演繹引入後緊接消元之局部迂迴（Detour）與序列演算之 `SCut` 規則可經主切歸約（Principal Cut Reduction）與交換秩歸約（Commutative Reduction）完全消除。
3. **定理 M4.T1（截斷命題反射與證明無關消元守衛定理）**：證明無關謂詞 `is_prop_irrelevant` 對 $\mathbf{1}, \mathbf{0}, \mathsf{Id}, \|A\|_{-1}$、乘積及餘域證明無關之 $\to, \Pi$ 封閉；截斷命題 $\|A\|_{-1}$ 僅允許消元至證明無關目標類型，構成證明相關類型至 Heyting 命題偏序集之伽羅瓦反射伴隨 $\mathsf{Squash} \dashv \mathsf{Incl}$。
4. **定理 M4.T2（Gentzen 主定理 Hauptsatz 與柯里-霍華德切消元交換圖定理）**：對任意序列推導 $\pi$，切消元演算法 `eliminate_cuts(π)` 嚴格達成 `count_cuts == 0`，且與編譯至證明項後之 $\beta$-正規化滿足嚴格交換圖：
   $$\mathsf{normalize\_ch\_term}(\mathsf{sequent\_to\_ch\_term}(\pi)) \;=\; \mathsf{normalize\_ch\_term}(\mathsf{sequent\_to\_ch\_term}(\mathsf{eliminate\_cuts}(\pi)))$$
5. **定理 M4.T3（Kolmogorov-Plotkin CPS 雙重否定古典嵌入定理）**：透過連續傳遞變換 $\neg\neg_R X := (X \to R) \to R$，古典排中律雙重否定 $\neg\neg(P \vee \neg P)$ 與古典 Peirce 定律 $\neg\neg(((A \to B) \to A) \to A)$ 皆具備機械驗證之直覺主義構造性證明項。
6. **定理 M4.T4（認證證明抹除與 $\forall\exists$ 見證程式提取定理）**：對任意良類型證明項 $\Gamma \vdash t : \Pi(x:D).\Sigma(y:D').P(x,y)$（其中 $P$ 為證明無關規格），`extract_computational_program` 完全抹除邏輯憑證子項為 $\square$（`EPErasedProp`），並精確提取純計算函數 $f : D \to D'$。

---

## 二、資料夾內已實作之演算法列表

| 演算法名稱 | 所在檔案 | 時間複雜度 | 功能與硬體/數據結構優化說明 |
| :--- | :--- | :--- | :--- |
| 公式 $\leftrightarrow$ 依賴類型雙向同構編譯器 (`formula_to_ch_type`, `ch_type_to_formula`) | `curry_howard_terms.mbt` | $O(\|\phi\|)$ | 嚴格保持雙層變數（物件變數與證明變數）分層索引 |
| BHK 自然演繹證明檢驗器與截斷守衛 (`infer_ch_term`, `is_prop_irrelevant`) | `curry_howard_terms.mbt` | $O(\|t\| \cdot \|\text{ty}\|)$ | 支援全稱/存在量化展開與證明無關消元安全檢查 |
| Prawitz 證明迂迴正規化引擎 (`normalize_ch_term`) | `curry_howard_terms.mbt` | 多項式於歸約步數 | 完整消除 $\to, \times, +, \Pi, \Sigma, \mathsf{Squash}$ 之全部 $\beta$-迂迴 |
| 序列演算結構弱化與證明項編譯器 (`weaken_sequent`, `sequent_to_ch_term`) | `cut_elim_cps_erasure.mbt` | $O(\|\pi\|)$ | 將 `SCut` 精確映射為顯式 $\beta$-紅基 `(λx. d2) d1` |
| Gentzen 構造性切消元引擎 (`eliminate_cuts`, `admissible_cut`) | `cut_elim_cps_erasure.mbt` | 有限終止歸約（切秩與公式度雙重良基歸納） | 處理公理切、矛盾切、左右交換切與合取/析取/蘊涵主切消元 |
| 古典 CPS 雙重否定公式與公理合成器 (`cps_translate_formula`, `synthesize_dn_excluded_middle`, `synthesize_cps_peirce`) | `cut_elim_cps_erasure.mbt` | $O(\|\phi\|)$ / 常數時間 $O(1)$ 見證建構 | 自動生成機械檢驗通過之排中律與 Peirce 律連續傳遞項 |
| 認證證明抹除與見證提取器 (`extract_computational_program`) | `cut_elim_cps_erasure.mbt` | $O(\|t\|)$ | 自動摺疊證明無關配對分量並提取純計算核心項 |

---

## 三、資料夾視角的依賴關係圖

```text
                  [ 外部上游依賴：無（純獨立基礎模組） ]
                                    │
                                    ▼
             ┌─────────────────────────────────────────────┐
             │         dtt/m4_curry_howard_prop            │
             │            curry_howard_terms.mbt           │
             │                      │                      │
             │                      ▼                      │
             │          cut_elim_cps_erasure.mbt           │
             └──────────────────────┬──────────────────────┘
                                    │
                                    ▼
                       [ dtt/m6_chu_galois_bridge ]
                                    │
                                    ▼
                        [ dtt/m7_unified_kernel ]
```

---

## 四、資料夾內動線及接入與輸出接口

### 內部資料動線
1. `curry_howard_terms.mbt` 建立物件項 `ObjTerm`、公式 `PropFormula`、類型 `CHType` 與證明項 `CHTerm`，提供雙向同構映射、雙層索引代換、證明類型合成與迂迴正規化。
2. `cut_elim_cps_erasure.mbt` 在 `curry_howard_terms.mbt` 之上實作序列演算 `SequentProof` 與切消元 `eliminate_cuts`、CPS 古典嵌入與 `ExtractedProg` 見證提取。

### 輸出公共接口（Public API）
- **類型與錯誤**：`DomainSort`, `ObjTerm`, `PropFormula`, `CHType`, `CHTerm`, `SequentProof`, `ExtractedProg`, `LogicError`。
- **同構、檢驗與正規化**：`shift_obj_term`, `subst_obj_term`, `formula_to_ch_type`, `ch_type_to_formula`, `shift_ch_type_obj`, `subst_ch_type_obj`, `is_prop_irrelevant`, `shift_ch_term`, `subst_ch_term`, `subst_ch_term_obj`, `infer_ch_term`, `normalize_ch_term`。
- **切消元、CPS 與認證抹除**：`count_cuts`, `weaken_sequent`, `sequent_to_ch_term`, `eliminate_cuts`, `cps_neg`, `cps_dneg`, `cps_translate_formula`, `synthesize_dn_excluded_middle`, `synthesize_cps_peirce`, `extract_computational_program`。
