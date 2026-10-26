
<a id="oet-733643513b9e4f98"></a>

## 第 4 章 算子链演算

将一组算子按次序连接后，每一步的输出成为下一步的输入，首尾之间的关系因而通过实际中间像域逐步传递。本章先研究有限算子链的距离界、零距传播与熵递推，再考察链长增加时的前缀乘积，最后讨论算子的因式分解、按域分段与局部替换。



<a id="oet-5a1b95150c3a4df2"></a>

### 4.1 算子链及其基本性质

**定义（算子链）**：$\mathcal X_{\mathrm{op}}$ 中的有限有序序列 $c=(\phi_1,\ldots,\phi_k)$ 称为**算子链**，$k\ge0$ 为其**长度**。该链依次施行 $\phi_1,\ldots,\phi_k$，其复合算子记为

$$
c_k=\phi_k\circ\cdots\circ\phi_1.
$$

长度为零的链为空序列，约定其复合算子为 $c_0=\operatorname{id}_{\mathcal X}$。由算子空间的复合封闭性（[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)），$c_k\in\mathcal X_{\mathrm{op}}$。链的长度属于指定的序列；不同的链可以具有相同的复合算子。

**定义（实际输入域序列）**：设 $c=(\phi_1,\ldots,\phi_k)$ 为算子链，取非空初始集 $U_1\subseteq\operatorname{dom}(c_k)$。递归定义

$$
U_{m+1}=\phi_m(U_m)\qquad(1\le m\le k).
$$

称 $\{U_m\}_{m=1}^{k+1}$ 为该链相对于 $U_1$ 的**实际输入域序列**。其中 $U_m$ 是第 $m$ 步的输入域（$1\le m\le k$），$U_{k+1}=c_k(U_1)$ 是最终像集；空链的序列仅含 $U_1$。

这些像集均非空。由于各算子保持吸收元，一旦某个中间输出为 $\bot$，最终输出也为 $\bot$；因此 $U_1\subseteq\operatorname{dom}(c_k)$ 保证 $U_m\subseteq\operatorname{dom}(\phi_m)$（$1\le m\le k$）。后续的受限矩阵均在相应的实际输入域上读取。

#### 距离向量递推

设给定的 $k$-步算子链具有复合算子 $c_k=\phi_k\circ\cdots\circ\phi_1$，取非空 $U_1\subseteq\operatorname{dom}(c_k)$，固定 $x,x'\in U_1$。令 $x_0=x$、$x'_0=x'$；对 $1\le m\le k$，令

$$
x_m=(\phi_m\circ\cdots\circ\phi_1)(x),
\qquad
x'_m=(\phi_m\circ\cdots\circ\phi_1)(x').
$$

定义各步中间像点的**距离向量**

$$
\mathbf d^{(m)}:=\bigl(d_j(x_m,x'_m)\bigr)_{j\in I}\in\bar{\mathbb R}_+^{|I|}
\qquad(0\le m\le k).
$$

于是 $\mathbf d^{(0)}=(d_j(x,x'))_{j\in I}$。沿上述实际输入域序列，有 $x_m,x'_m\in U_{m+1}$（$0\le m\le k$）。

> **约定（向量与矩阵的不等式）**：除另有说明外，向量之间的 $\leq$、$\geq$ 均按分量理解，矩阵之间的 $\leq$、$\geq$ 均按条目理解。

若对各个 $0\le m<k$，已在实际输入域上选取合法证书

$$
\mathbf L^{(m+1)}\in\mathscr L(\phi_{m+1})\big|_{U_{m+1}},
\qquad
\mathbf K^{(m+1)}\in\mathscr K(\phi_{m+1})\big|_{U_{m+1}},
$$

并记 $\mathbf N^{(m+1)}=\mathbf N(\phi_{m+1})\big|_{U_{m+1}}$，则对每个输出分量 $j\in I$，

$$
d_j^{(m+1)} \begin{cases} = 0 & \text{若存在 } i \in I \text{ 使得 } d_i^{(m)} < [\mathbf{N}^{(m+1)}]_{ji} \\[6pt] \in \left[\displaystyle\sum_{i \in I} K^{(m+1)}_{i \to j} \cdot d_i^{(m)},\;\; \displaystyle\sum_{i \in I} L^{(m+1)}_{i \to j} \cdot d_i^{(m)}\right] & \text{否则} \end{cases}
$$

> **注（截断判据所用的统一零化下界）**：$[\mathbf{N}^{(m+1)}]_{ji} = \underline{r}^{\mathrm N}_{\phi_{m+1}, i, j}\big|_{U_{m+1}}$ 是零化半径的下确界（[§ 3.3](<03-operator-local-degeneracy.md#user-content-oet-bb1487a09d8bf151>)）。递推式只使用这个统一下界作为截断的充分判据，不使用各基点的点态零化半径。

这在 $\bar{\mathbb{R}}_+^{|I|}$ 上给出**分段的距离向量约束**：$\mathbf{N}$ 给出截断充分判据，$\mathbf{L}$ 给出上界，$\mathbf{K}$ 给出下界。

#### 链级零化与熵递推


<a id="oet-9a65248d646a2b6f"></a>

**命题 4.1（算子链中的纤维截断与零距传播）**：设

$$
c_k=\phi_k\circ\cdots\circ\phi_1,\qquad k\ge 1,
$$

取 $U_1\subseteq \mathrm{dom}(c_k)$，并令 $U_{r+1}=\phi_r(U_r)$（$r=1,\ldots,k$）。对任意 $x,x'\in U_1$，定义

$$
x_0=x,\quad x'_0=x',\qquad
x_m=(\phi_m\circ\cdots\circ\phi_1)(x),\quad
x'_m=(\phi_m\circ\cdots\circ\phi_1)(x')\quad (1\le m\le k).
$$

则 $x_m,x'_m\in U_{m+1}$（$0\le m<k$）。

**(i)** 若对某个 $0\le m<k$ 有

$$
x'_m\in \operatorname{Fib}_{\phi_{m+1},j}\bigl(\phi_{m+1}(x_m)\mid U_{m+1}\bigr),
$$

则

$$
d_j(x_{m+1},x'_{m+1})=0.
$$

**(ii)** 更一般地，若某一级 $s$ 满足 $0\le s\le q\le k$ 且

$$
d_l(x_s,x'_s)=0,\qquad \forall l\in I,
$$

并且对每个 $p=s+1,\ldots,q$ 存在合法 Lip 矩阵

$$
\mathbf{L}^{(p)}\in \mathscr{L}(\phi_p)\big|_{U_p},
$$

则

$$
d_l(x_q,x'_q)=0,\qquad \forall l\in I.
$$

**证明**：由 $U_{r+1}=\phi_r(U_r)$ 的递推定义，$x_m,x'_m\in U_{m+1}$。从第 $m$ 级到第 $m+1$ 级的截断结论是 [命题 3.11](<03-operator-local-degeneracy.md#user-content-oet-70882b889ff4ec94>) 对 $\phi_{m+1}$、$U_{m+1}$、$x_m$ 与 $x'_m$ 的直接应用。

若 $q=s$，结论正是前提。以下设 $q>s$。若第 $s$ 级满足全分量零距，则对任意 $p=s+1,\ldots,q$，Lip 不等式给出

$$
d_j(x_p,x'_p)
\le
\sum_{l\in I} L^{(p)}_{l\to j}\, d_l(x_{p-1},x'_{p-1})
=0,\qquad \forall j\in I,
$$

其中最后等号使用 $\bar{\mathbb{R}}_+$ 中 $a\cdot 0=0$（包括 $a=+\infty$）。由数学归纳，$x_q$ 与 $x'_q$ 在所有分量上零测距。$\square$


<a id="oet-664ab4248e21a8a0"></a>

**命题 4.2（算子链的零化矩阵下界）**：设算子链的复合为 $c_k = \phi_k \circ \cdots \circ \phi_1 \in \mathcal{X}_{\mathrm{op}}$（$k \ge 2$），指定非空初始子集 $U_1 \subseteq \mathrm{dom}(c_k)$，令实际输入域序列为 $U_{m+1} = \phi_m(U_m)$（$m = 1, \ldots, k$）。设各后续层算子在对应像集上存在合法 Lip 矩阵 $\mathbf L^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$（$m = 2, \ldots, k$）。则复合零化矩阵满足：

$$
[\mathbf{N}(c_k)\big|_{U_1}]_{ji} \;\geq\; \min_{l \in I} [\mathbf{N}(\phi_1)\big|_{U_1}]_{li}
$$

即：对任意 $y\in U_1$ 及有限正数 $r < \min_{l \in I} [\mathbf{N}(\phi_1)\big|_{U_1}]_{li}$，首层算子 $\phi_1$ 在 $B_i(y, r) \cap U_1$ 内将**所有分量**归零（$d_l(\phi_1(x), \phi_1(y)) = 0$，$\forall l$），从而全链在同一球内对 $d_j$ 亦归零。

**证明**：令

$$
M=\min_{l\in I}[\mathbf N(\phi_1)\big|_{U_1}]_{li}.
$$

若 $M=0$，结论平凡。以下设 $M>0$。

取任意 $0 < r < M$，任意基点 $y \in U_1$，任意 $x \in B_i(y, r) \cap U_1$：

对任意 $l\in I$，有

$$
r<M\leq[\mathbf N(\phi_1)\big|_{U_1}]_{li}
\leq
r^{\mathrm N}_{\phi_1,i,l}(y\mid U_1).
$$

由于 $r^{\mathrm N}_{\phi_1,i,l}(y\mid U_1)$ 是合法半径集的上确界且 $r$ 严格小于该上确界，存在合法半径 $\rho>r$ 使

$$
B_i(y,\rho)\cap U_1
\subseteq
\operatorname{Fib}_{\phi_1,l}(\phi_1(y)\mid U_1).
$$

因此

$$
B_i(y,r)\cap U_1
\subseteq
\operatorname{Fib}_{\phi_1,l}(\phi_1(y)\mid U_1).
$$

由于 $x\in B_i(y,r)\cap U_1$，得到

$$
d_l(\phi_1(x),\phi_1(y))=0
\qquad(\forall l\in I).
$$

由 [命题 4.1](<#user-content-oet-9a65248d646a2b6f>)(ii)，取起始层 $s=1$、终止层 $q=k$，首层所得的全分量零距沿后续 Lip 矩阵逐层保持，故 $d_j(c_k(x),c_k(y))=0$。

由此，对任意 $0<r<M$，

$$
B_i(y,r)\cap U_1
\subseteq
\operatorname{Fib}_{c_k,j}(c_k(y)\mid U_1),
$$

故

$$
r^{\mathrm N}_{c_k,i,j}(y\mid U_1)\ge r.
$$

令 $r\uparrow M$，得到 $r^{\mathrm N}_{c_k,i,j}(y\mid U_1)\ge M$；当 $M=+\infty$ 时，该结论表示对任意有限 $r$ 均成立。再对 $y\in U_1$ 取下确界，即

$$
[\mathbf N(c_k)\big|_{U_1}]_{ji}\ge M.
$$

证毕。$\square$

> **注（非平凡性条件）**：$\min_l [\mathbf{N}(\phi_1)\big|_{U_1}]_{li} > 0$ 在本命题中表示存在统一的正半径，使每个基点的 $d_i$-球与 $U_1$ 的交集同时落入所有输出分量的零距纤维。若该最小值为 $0$，本命题只给出 $0$ 下界；是否具有正零化半径还需另行判断。

沿同一算子链，还可以比较初始集与逐步像集的度量熵。


<a id="oet-2cb9c1e3d59895b0"></a>

**推论 4.3（算子链的熵递推等式）**：设 $c_k = \phi_k \circ \cdots \circ \phi_1$（$k\ge0$），固定分量 $i\in I$ 与有限正精度 $\varepsilon$。取非空 $U_1\subseteq\operatorname{dom}(c_k)$，令 $U_{m+1}=\phi_m(U_m)$（$1\le m\le k$）。若各 $U_m$（$1\le m\le k+1$）的度量熵 $E_{\varepsilon,i}(U_m)$ 均为有限实数，则

$$
E_{\varepsilon, i}(U_{k+1}) \;=\; E_{\varepsilon, i}(U_1) \;-\; \sum_{m=1}^{k} \Delta E_{\varepsilon, i}(\phi_m \mid U_m)
$$

**证明**：由实际输入域序列的性质，$U_m\subseteq\operatorname{dom}(\phi_m)$（$1\le m\le k$）。各步两端熵均有限，故映射熵差良定，并且

$$
\begin{aligned}
\sum_{m=1}^k\Delta E_{\varepsilon,i}(\phi_m\mid U_m)
&=\sum_{m=1}^k\bigl(E_{\varepsilon,i}(U_m)-E_{\varepsilon,i}(U_{m+1})\bigr)\\
&=E_{\varepsilon,i}(U_1)-E_{\varepsilon,i}(U_{k+1}).
\end{aligned}
$$

第二等式由有限实数列的相邻差相消得到，移项即得结论。$k=0$ 时求和为空，等式仍成立。$\square$

> **注（熵递推与有限步归零）**：在各步参与运算的熵均有限时，[推论 4.3](<#user-content-oet-2cb9c1e3d59895b0>) 把链尾熵写成初始熵减去前缀熵差和。一致正熵差下界下的有限步归零估计见 [习题 4.3](<#mb-exercise-oet-b7e77b504317782a>)。


<a id="oet-36b3776ed03a6cb4"></a>

### 4.2 长链的前缀乘积分析


为考察链长增加时的距离变化，本节沿实际输入域选取各步的 L/K 证书，并研究其有序乘积。沿用 [推论 2.5](<02-operator-bounds.md#user-content-oet-c80171fa685dc795>) 的括号上标约定：$\mathbf L^{(m)}$ 与 $\mathbf K^{(m)}$ 表示第 $m$ 步证书。设

$$
c_k=\phi_k\circ\cdots\circ\phi_1,\qquad
U_{m+1}=\phi_m(U_m).
$$

在每一步的实际输入域 $U_m$ 上，分别选取证书

$$
\mathbf L^{(m)}\in\mathscr L(\phi_m)\big|_{U_m},
\qquad
\mathbf K^{(m)}\in\mathscr K(\phi_m)\big|_{U_m}.
$$

**约定（矩阵乘积的顺序）**：相应的有序前缀乘积写为

$$
\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}:=\mathbf L^{(k)}\cdots\mathbf L^{(1)},
\qquad
\overleftarrow{\prod}_{r=1}^{k}\mathbf K^{(r)}:=\mathbf K^{(k)}\cdots\mathbf K^{(1)}.
$$

箭头表示较大指标的矩阵写在左侧；空乘积取单位矩阵 $\mathbf I$。

当同一个证书反复使用时，前缀乘积成为矩阵幂，可以进一步用谱半径估计。本节的谱分析限定于有限值矩阵。


<a id="oet-95d270a294f96c14"></a>

**命题 4.4（一般链前缀乘积的渐近判据）**：设 $(\phi_m)_{m\ge1}\subseteq\mathcal X_{\mathrm{op}}$，取非空集合 $U_1$，递归定义 $U_{m+1}=\phi_m(U_m)$，并假设 $U_m\subseteq\operatorname{dom}(\phi_m)$ 对所有 $m\ge1$ 成立。对每个 $k\ge1$，令 $c_k=\phi_k\circ\cdots\circ\phi_1$。

**(i)（L 前缀乘积）** 若对每个 $m$ 选取

$$
\mathbf L^{(m)}\in\mathscr L(\phi_m)\big|_{U_m},
$$

则

$$
\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}\in\mathscr L(c_k)\big|_{U_1},
$$

并且对任意 $x,x'\in U_1$ 与 $j\in I$，

$$
d_j(c_k(x),c_k(x'))
\le
\sum_{i\in I}\left[\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}\right]_{i\to j}\,d_i(x,x').
$$

若固定 $x,x'\in U_1$、$j\in I$，且

$$
\sum_{i\in I}\left[\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}\right]_{i\to j}\,d_i(x,x')\to0,
$$

则 $d_j(c_k(x),c_k(x'))\to0$。特别地，若 $d_i(x,x')<+\infty$ 对所有 $i\in I$ 成立，且对所有 $i\in I$ 都有

$$
\left[\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}\right]_{i\to j}\to0,
$$

则上述收敛成立。

**(ii)（K 前缀乘积）** 若对每个 $m$ 选取

$$
\mathbf K^{(m)}\in\mathscr K(\phi_m)\big|_{U_m},
$$

则

$$
\overleftarrow{\prod}_{r=1}^{k}\mathbf K^{(r)}\in\mathscr K(c_k)\big|_{U_1},
$$

并且对任意 $x,x'\in U_1$ 与 $j\in I$，

$$
d_j(c_k(x),c_k(x'))
\ge
\sum_{i\in I}\left[\overleftarrow{\prod}_{r=1}^{k}\mathbf K^{(r)}\right]_{i\to j}\,d_i(x,x').
$$

对固定 $x,x'\in U_1$，若存在 $i,j\in I$ 与子序列 $k_n$ 使

$$
\left[\overleftarrow{\prod}_{r=1}^{k_n}\mathbf K^{(r)}\right]_{i\to j}\to+\infty,
$$

且 $d_i(x,x')>0$，则 $d_j(c_{k_n}(x),c_{k_n}(x'))\to+\infty$。

**证明**：由 $U_m\subseteq\operatorname{dom}(\phi_m)$ 与 $U_{m+1}=\phi_m(U_m)$ 逐步递推，得到

$$
U_1\subseteq\operatorname{dom}(c_k)
\qquad(k\ge1).
$$

因此可应用有限复合的局部矩阵界 [推论 2.5](<02-operator-bounds.md#user-content-oet-c80171fa685dc795>)，得到

$$
\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}\in\mathscr L(c_k)\big|_{U_1},
\qquad
\overleftarrow{\prod}_{r=1}^{k}\mathbf K^{(r)}\in\mathscr K(c_k)\big|_{U_1}.
$$

将 Lip 与 co-Lip 定义分别写到点对 $x,x'\in U_1$ 上，即得两组不等式。

L 情形中，若右侧上界趋于 $0$，由非负性和夹逼得到 $d_j(c_k(x),c_k(x'))\to0$。若每个源分量初始距离有限且各条目 $\left[\overleftarrow{\prod}_{r=1}^{k}\mathbf L^{(r)}\right]_{i\to j}\to0$，由于 $I$ 有限，有限和也趋于 $0$。

K 情形中，

$$
d_j(c_{k_n}(x),c_{k_n}(x'))
\ge
\left[\overleftarrow{\prod}_{r=1}^{k_n}\mathbf K^{(r)}\right]_{i\to j}\,d_i(x,x').
$$

若 $0<d_i(x,x')<+\infty$，右侧趋于 $+\infty$；若 $d_i(x,x')=+\infty$，则在 $\left[\overleftarrow{\prod}_{r=1}^{k_n}\mathbf K^{(r)}\right]_{i\to j}>0$ 的尾段右侧为 $+\infty$。因此目标分量沿该子序列趋于 $+\infty$。$\square$

记 $\rho(\mathbf M)$ 为有限非负矩阵 $\mathbf M$ 的谱半径。下列命题只处理同一个有限值证书在同一不变域上反复使用的情形。


<a id="oet-cb1aac0882bde4ae"></a>

**命题 4.5（常系数 L/K 证书的谱充分判据）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$U\subseteq\operatorname{dom}(\phi)$，且 $\phi(U)\subseteq U$。

**(i)（L 收缩充分证书）** 若存在有限值 Lip 矩阵

$$
\mathbf L\in\mathscr L(\phi)\big|_U\cap[0,+\infty)^{|I|\times |I|}
$$

满足 $\rho(\mathbf L)<1$，则对每个 $k\ge1$ 有 $\mathbf L^k\in\mathscr L(\phi^k)\big|_U$，且对任意 $x,x'\in U$、$j\in I$，

$$
d_j(\phi^k(x),\phi^k(x'))
\le
\sum_{i\in I}[\mathbf L^k]_{i\to j}d_i(x,x').
$$

若进一步 $d_i(x,x')<+\infty$ 对所有 $i\in I$ 成立，则 $d_j(\phi^k(x),\phi^k(x'))\to0$。

**(ii)（K 子序列扩张证书）** 若存在有限值 co-Lip 矩阵

$$
\mathbf K\in\mathscr K(\phi)\big|_U\cap[0,+\infty)^{|I|\times |I|},
$$

则对每个 $k\ge1$ 有 $\mathbf K^k\in\mathscr K(\phi^k)\big|_U$，且对任意 $x,x'\in U$、$j\in I$，

$$
d_j(\phi^k(x),\phi^k(x'))
\ge
\sum_{i\in I}[\mathbf K^k]_{i\to j}d_i(x,x').
$$

若存在 $i,j\in I$ 与正整数子序列 $k_n\to+\infty$ 使 $[\mathbf K^{k_n}]_{i\to j}\to+\infty$，且 $d_i(x,x')>0$，则 $d_j(\phi^{k_n}(x),\phi^{k_n}(x'))\to+\infty$。特别地，当 $\rho(\mathbf K)>1$ 时，有限非负矩阵幂不可能逐条目有界；由于 $I^2$ 有限，存在固定的 $i,j\in I$ 与正整数子序列 $k_n$ 使 $[\mathbf K^{k_n}]_{i\to j}\to+\infty$。对于任何满足 $d_i(x,x')>0$ 的点对，因而适用上述结论。

**证明**：由 $\phi(U)\subseteq U$，同一个证书可在每一步限制到实际像域

$$
U_m=\phi^{m-1}(U).
$$

对任意 $k\ge1$，[推论 2.5](<02-operator-bounds.md#user-content-oet-c80171fa685dc795>) 给出

$$
\mathbf L^k\in\mathscr L(\phi^k)\big|_U,\qquad
\mathbf K^k\in\mathscr K(\phi^k)\big|_U.
$$

点态不等式由 Lip 与 co-Lip 定义直接得到。

若 $\rho(\mathbf L)<1$，有限非负矩阵幂满足 $\mathbf L^k\to\mathbf0$，故有限初始距离下右侧有限和趋于 $0$。

K 分支的子序列结论由下界不等式直接给出。若 $\rho(\mathbf K)>1$ 而每个条目序列 $[\mathbf K^k]_{i\to j}$ 都有界，则有限个条目的共同上界将使任一矩阵范数下的 $\|\mathbf K^k\|$ 有界，与谱半径公式给出的指数增长矛盾。故至少一个固定条目无界；从该非负无界序列中可选取趋于 $+\infty$ 的子序列。$\square$

> **注（谱判据的适用范围）**：[命题 4.5](<#user-content-oet-cb1aac0882bde4ae>) 只在其两个充分条件分支内给出结论；对 $\rho(\mathbf L)\ge1$ 或 $\rho(\mathbf K)\le1$ 的情形，本命题不作实际映射行为结论。若沿实际像域选取随 $m$ 变化的局部证书，则应回到 [命题 4.4](<#user-content-oet-95d270a294f96c14>) 的前缀乘积。


<a id="oet-92938f295a2b0333"></a>

### 4.3 代数因式分解

前两节从给定的算子链估计复合结果。下面反过来固定一个算子，考察它能否分解为若干次作用的复合；本节先讨论不附加距离约束的代数分解。

**定义（代数因式分解）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$。称 $\phi$ 在幺半群 $(\mathcal{X}_{\mathrm{op}}, \circ, \mathrm{id}_{\mathcal{X}})$ 中**可因式分解**，若存在 $\phi_1, \phi_2 \in \mathcal{X}_{\mathrm{op}}$（$\phi_1 \neq \mathrm{id}$，$\phi_2 \neq \mathrm{id}$）使得 $\phi = \phi_2 \circ \phi_1$。否则称 $\phi$ 为**不可约算子**。这里排除了恒等因子，因为 $\phi = \phi \circ \mathrm{id} = \mathrm{id} \circ \phi$ 是幺半群中的平凡分解。

以下只讨论保持吸收元的全体自映射，不限制因子的 Lip、co-Lip、零化数据或局部结构。


<a id="oet-a09c6a96d9cd476a"></a>

**命题 4.6（算子的普遍可分解性）**：设 $|\mathcal{X}| \geq 4$。则 $(\mathcal{X}_{\mathrm{op}}, \circ, \mathrm{id}_{\mathcal{X}})$ 中**每个**算子 $\phi \in \mathcal{X}_{\mathrm{op}}$（包括 $\mathrm{id}_{\mathcal{X}}$ 自身）均可因式分解——$\mathcal{X}_{\mathrm{op}}$ 中不存在不可约算子。

**证明**：取三个互异的非吸收点 $a,b,c$。对换 $(a\;b)$ 与 $(a\;c)$ 均固定 $\bot$，且彼此不同，故其中至少有一个不同于 $\phi$，记为 $\tau$。令

$$
\phi_1=\tau,\qquad \phi_2=\phi\circ\tau.
$$

由于 $\tau\circ\tau=\operatorname{id}_{\mathcal X}$，有 $\phi_2\circ\phi_1=\phi$。两个因子均保持吸收元，且 $\phi_1\ne\operatorname{id}_{\mathcal X}$。若 $\phi_2=\operatorname{id}_{\mathcal X}$，则 $\phi=\phi\circ\tau\circ\tau=\tau$，与所选 $\tau\ne\phi$ 矛盾。因此该分解的两个因子都不是恒等算子。$\square$


<a id="oet-a2b0697cd3c2decb"></a>

> **注（三点空间上的不可约算子）**：[命题 4.6](<#user-content-oet-a09c6a96d9cd476a>) 的基数前提不能直接去掉。当 $\mathcal{X}=\{\bot,a,b\}$ 时，对换 $\tau(a)=b,\tau(b)=a,\tau(\bot)=\bot$ 在 $(\mathcal{X}_{\mathrm{op}},\circ,\mathrm{id}_{\mathcal{X}})$ 中不可因式分解。
>
> **证明**：若 $\tau=\phi_2\circ\phi_1$，且 $\phi_1,\phi_2\neq\mathrm{id}$。由
>
> $$
> \phi_2(\phi_1(a))=b,\qquad \phi_2(\phi_1(b))=a
> $$
>
> 可知 $\phi_1(a)$ 与 $\phi_1(b)$ 不能等于 $\bot$，且二者不相等。因此 $\{\phi_1(a),\phi_1(b)\}=\{a,b\}$。若 $\phi_1$ 在 $\{a,b\}$ 上为恒等，则 $\phi_1=\mathrm{id}$，矛盾；若 $\phi_1=\tau$，则 $\phi_2$ 必须在 $\{a,b\}$ 上为恒等且固定 $\bot$，故 $\phi_2=\mathrm{id}$，矛盾。因此不存在这样的非平凡因式分解。$\square$

> **注（不可约性的使用范围）**：上述结论针对保持吸收元的全体自映射。若限制允许的因子类别，例如要求因子满足指定的 Lip 或 co-Lip 条件，则应在该类别中重新定义并考察不可约性。

给定因式分解后，各因子的 Lip 与 co-Lip 证书按复合律（[命题 2.2](<02-operator-bounds.md#user-content-oet-193cebcc1a7f9259>)、[命题 2.4](<02-operator-bounds.md#user-content-oet-0f256e6f1d38a612>)）给出复合算子的界；统一零化半径的复合下界见 [命题 3.12](<03-operator-local-degeneracy.md#user-content-oet-1217d1061a2c95ce>)。


<a id="oet-e84832eedce36d68"></a>

### 4.4 域限制与分段构造

**定义（域限制算子）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$，非空子集 $U \subseteq \mathrm{dom}(\phi)$。定义**域限制算子** $\phi\big|_U: \mathcal{X} \to \mathcal{X}$：

$$
\phi\big|_U(x) = \begin{cases} \phi(x) & x \in U \\ \bot & x \notin U \end{cases}
$$

因 $U \subseteq \mathrm{dom}(\phi)$ 且 $\bot \notin \mathrm{dom}(\phi)$（[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>)），有 $\bot \notin U$，故 $\phi\big|_U(\bot) = \bot$。因此 $\phi\big|_U \in \mathcal{X}_{\mathrm{op}}$，$\mathrm{dom}(\phi\big|_U) = U$。

> **注（$\bot$-补全的代数意义）**：域限制通过吸收元 $\bot$ 实现偏函数的全函数化，保持 $\mathcal{X}_{\mathrm{op}}$ 空间归属。受限矩阵的计算范围仍由记号 $\big|_U$ 指定；域外取 $\bot$ 只负责把限制对象重新放回全函数空间。


<a id="oet-a63623c9504af642"></a>

**命题 4.7（域限制与复合的相容性）**：设 $\phi_1, \phi_2 \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$（$U \neq \emptyset$）。则：

$$
(\phi_2 \circ \phi_1)\big|_U \;=\; \phi_2\big|_{\phi_1(U)} \circ \phi_1\big|_U
$$

即域限制与复合相容：限制复合等于逐步限制后再复合，其中中间域为 $\phi_1(U)$。

**证明**：由 $U\subseteq\operatorname{dom}(\phi_2\circ\phi_1)$，有 $U\subseteq\operatorname{dom}(\phi_1)$ 及 $\phi_1(U)\subseteq\operatorname{dom}(\phi_2)$，故等式右侧的两个域限制均已定义。

对 $x \in U$，有

$$
(\phi_2 \circ \phi_1)\big|_U(x)=\phi_2(\phi_1(x)).
$$

右侧满足

$$
\phi_1\big|_U(x)=\phi_1(x),\qquad \phi_1(x)\in\phi_1(U),
$$

故

$$
\phi_2\big|_{\phi_1(U)}(\phi_1(x))=\phi_2(\phi_1(x)).
$$

对 $x \notin U$，有

$$
(\phi_2 \circ \phi_1)\big|_U(x)=\bot.
$$

右侧满足 $\phi_1\big|_U(x)=\bot$。又因为 $\bot \notin \mathrm{dom}(\phi_1)\supseteq U$，$\phi_1$ 在 $U$ 上的像不含 $\bot$，即

$$
\bot\notin\phi_1(U).
$$

故

$$
\phi_2\big|_{\phi_1(U)}(\bot)=\bot.
$$

两边对所有 $x\in\mathcal X$ 取值相同，结论成立。$\square$

> **约定（全域记号）**：沿用 $\mathscr L(\phi)$ 的全域记号。当 $\mathrm{dom}(\phi)\ne\emptyset$ 时，也简记 $\mathscr K(\phi):=\mathscr K(\phi)\big|_{\mathrm{dom}(\phi)}$、$\mathbf N(\phi):=\mathbf N(\phi)\big|_{\mathrm{dom}(\phi)}$。


<a id="oet-3d5f909fa9f5d7da"></a>

**命题 4.8（受限域上的证书单调性）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi)$（$U \neq \emptyset$）。则：

**(i)（Lip 矩阵族的包含关系）**：$\mathscr{L}(\phi) \subseteq \mathscr{L}(\phi)\big|_U$。即任何全域 Lip 矩阵在局部仍然有效。

**(ii)（co-Lip 矩阵族的包含关系）**：$\mathscr{K}(\phi) \subseteq \mathscr{K}(\phi)\big|_U$。即任何全域 co-Lip 矩阵在局部仍然有效。

**(iii)（零化扩大）**：$[\mathbf{N}(\phi)]_{ji} \leq [\mathbf{N}(\phi)\big|_U]_{ji}$（逐元素）。即 $\underline{r}^{\mathrm N}_{\phi, d_i, d_j}\big|_U \geq \underline{r}^{\mathrm N}_{\phi, d_i, d_j}$：受限域上的统一零化半径不小于全定义域上的值。

**证明**：在 [引理 2.1](<02-operator-bounds.md#user-content-oet-4ff5c58d71e1651f>)、[引理 2.3](<02-operator-bounds.md#user-content-oet-893b1d33535f7245>) 中取 $V=\operatorname{dom}(\phi)$，分别得到 (i)、(ii)。在 [命题 3.14](<03-operator-local-degeneracy.md#user-content-oet-451ca2134cd62db4>)(ii) 中取 $f=\phi$、$A=\operatorname{dom}(\phi)$、$B=U$，再按零化矩阵的定义逐条目读取，即得 (iii)。$\square$

> **注（受限域证书的局部性）**：[命题 4.8](<#user-content-oet-3d5f909fa9f5d7da>) 是域分解的代数基础：后续只在实际使用的子域上读取 L/K/N 证书，而不把全域证书视为唯一有效描述。

#### 定义域分划与分段算子

**定义（定义域分划）**：设 $U \subseteq \mathcal{X}$（$U \neq \emptyset$），有限族 $\{U_m\}_{m=1}^M$（$M \geq 1$）称为 $U$ 的**分划**，若：$U_m \neq \emptyset$（$\forall m$），$U_m \cap U_n = \emptyset$（$m \neq n$），$\bigsqcup_{m=1}^M U_m = U$。

**定义（分段算子）**：设 $\{U_m\}_{m=1}^M$ 为 $U$ 的分划，$\{\phi_m \in \mathcal{X}_{\mathrm{op}}\}_{m=1}^M$ 为对应的**局域算子族**，且 $U_m \subseteq \mathrm{dom}(\phi_m)$（$\forall m$）。定义**分段算子** $\psi: \mathcal{X} \to \mathcal{X}$：

$$
\psi(x) = \begin{cases} \phi_m(x) & x \in U_m \\ \bot & x \notin U \end{cases}
$$

由分划的互斥穷尽性，$\psi$ 在 $U$ 上良定义。$\mathrm{dom}(\psi) = U$。因 $U_m \subseteq \mathrm{dom}(\phi_m)$ 且 $\bot \notin \mathrm{dom}(\phi_m)$（[§ 1.3](<01-foundations.md#user-content-oet-57a1dc05727a3772>) 约定），有 $\bot \notin U_m$（$\forall m$），从而 $\bot \notin U$，故 $\psi(\bot) = \bot$，$\psi \in \mathcal{X}_{\mathrm{op}}$。


<a id="oet-b4f65e22f18fce79"></a>

**推论 4.9（域分解与合成恒等式）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\{U_m\}_{m=1}^M$ 为非空集 $U\subseteq\mathrm{dom}(\phi)$ 的分划。将各域限制算子 $\phi\big|_{U_m}$ 拼接为分段算子 $\psi$，则

$$
\psi=\phi\big|_U.
$$

并且 $\psi=\phi$ 当且仅当 $U=\mathrm{dom}(\phi)$。

**证明**：若 $x\in U$，取其所属分划块 $U_m$，则 $\psi(x)=\phi\big|_{U_m}(x)=\phi(x)$；若 $x\notin U$，则 $\psi(x)=\bot$。这正是 $\phi\big|_U$ 的定义，故 $\psi=\phi\big|_U$。

若 $\psi=\phi$，由 $\mathrm{dom}(\psi)=U$ 得 $U=\mathrm{dom}(\phi)$。反之，若 $U=\mathrm{dom}(\phi)$，则 $\phi$ 在 $U$ 外也取值 $\bot$，故 $\phi\big|_U=\phi$，从而 $\psi=\phi$。$\square$

> **约定（逐条目极值记号）**：$\inf \mathscr{L}(\phi)\big|_U$ 与 $\sup \mathscr{K}(\phi)\big|_U$ 均指矩阵族中各条目分别取逐条目 $\inf$ 或 $\sup$，不蕴含该极值被某个矩阵族元素同时取到。若矩阵族为空，约定 $\inf \emptyset = +\infty$（Lip 无合法证书）、$\sup \emptyset = 0$（co-Lip 无下界保证）。


<a id="oet-5846008cae9ea67d"></a>

**命题 4.10（分段合成的全域证书比较界）**：设 $\psi$ 是由 $U$ 的分划 $\{U_m\}_{m=1}^M$ 与局域算子族 $\{\phi_m\}_{m=1}^M$ 按上述定义拼接得到的分段算子。则 $\psi$ 在全域 $U$ 上的受限矩阵满足：

**(i)（全域 Lip 条目的下界）**：对**任意** $\mathbf{L} \in \mathscr{L}(\psi)\big|_U$，

$$
[L]_{i \to j} \;\geq\; \max_m \inf_{\mathbf{L}_m \in \mathscr{L}(\phi_m)|_{U_m}} [L_m]_{i \to j}
$$

等价地，$\inf \mathscr{L}(\psi)\big|_U \geq \max_m \inf \mathscr{L}(\phi_m)\big|_{U_m}$（逐条目 $\inf$）。跨分区点对属于 $U$ 内点对，因而会施加各局域证书中没有出现的额外约束；上述不等式本身不提供有限条目保证。

**(ii)（全域 co-Lip 条目的上界）**：对**任意** $\mathbf{K} \in \mathscr{K}(\psi)\big|_U$，

$$
[K]_{i \to j} \;\leq\; \min_m \sup_{\mathbf{K}_m \in \mathscr{K}(\phi_m)|_{U_m}} [K_m]_{i \to j}
$$

等价地，$\sup \mathscr{K}(\psi)\big|_U \leq \min_m \sup \mathscr{K}(\phi_m)\big|_{U_m}$（逐条目 $\sup$）。且若存在跨分区点对 $x \in U_m$、$x' \in U_n$（$m \neq n$）使得 $d_i(x, x') > 0$ 但 $d_j(\phi_m(x), \phi_n(x')) = 0$，则 $\sup_{K \in \mathscr{K}(\psi)|_U} [K]_{i \to j} = 0$。

**证明**：

**(i)** 取 $\mathbf L\in\mathscr L(\psi)\big|_U$。固定分划块 $U_m$，并取任意 $x,y\in U_m$。由分段算子的定义，

$$
\psi(x)=\phi_m(x),\qquad
\psi(y)=\phi_m(y).
$$

因此对每个 $j\in I$，

$$
d_j(\phi_m(x),\phi_m(y))
=d_j(\psi(x),\psi(y))
\leq
\sum_{i\in I}[L]_{i\to j}d_i(x,y).
$$

这说明同一个矩阵 $\mathbf L$ 在 $U_m$ 上也是 $\phi_m$ 的合法 Lip 矩阵，即

$$
\mathbf L\in\mathscr L(\phi_m)\big|_{U_m}.
$$

由于 $m$ 任意，

$$
\mathscr L(\psi)\big|_U
\subseteq
\mathscr L(\phi_m)\big|_{U_m}
\qquad(\forall m).
$$

对每个条目取下确界，得到

$$
\inf\mathscr L(\psi)\big|_U
\geq
\inf\mathscr L(\phi_m)\big|_{U_m}
\qquad(\forall m).
$$

再对 $m$ 取 $\max$，即得 (i)。跨分区点对也属于 $U$ 内点对，因此会对 $\mathbf L$ 施加各局域证书中没有出现的额外约束；所得不等式不保证逐条目下确界有限。

**(ii)** 取 $\mathbf K\in\mathscr K(\psi)\big|_U$。固定 $m$ 并限制到 $U_m$ 内点对。由 $\psi|_{U_m}=\phi_m|_{U_m}$，$\mathbf K$ 也是 $\phi_m$ 在 $U_m$ 上的合法 co-Lip 矩阵。因此逐条目有

$$
[K]_{i\to j}
\leq
\sup_{\mathbf K_m\in\mathscr K(\phi_m)|_{U_m}}[K_m]_{i\to j}
\qquad(\forall m).
$$

对 $m$ 取 $\min$ 即得 co-Lip 条目的全域上界。

若存在跨分区点对 $x\in U_m$、$x'\in U_n$（$m\neq n$）使

$$
d_i(x,x')>0,\qquad
d_j(\psi(x),\psi(x'))=d_j(\phi_m(x),\phi_n(x'))=0,
$$

则对任意 $\mathbf K\in\mathscr K(\psi)\big|_U$，co-Lip 不等式给出

$$
[K]_{i\to j}d_i(x,x')
\leq
d_j(\psi(x),\psi(x'))
=0.
$$

由 $d_i(x,x')>0$ 与非负性，必有 $[K]_{i\to j}=0$。因此对应条目的逐条目 $\sup$ 也为 $0$。$\square$


<a id="oet-a1caa879309ff2e3"></a>

### 4.5 局部等价与替换

比较两个算子时，可以只考察它们在某个共同定义的子集上，是否对每个输入给出相同的输出。为描述这种一致性，我们引入局部等价的概念。

**定义（局部等价）**：设 $\phi, \psi \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi) \cap \mathrm{dom}(\psi)$（$U \neq \emptyset$）。称 $\phi$ 与 $\psi$ 在 $U$ 上**局部等价**，记 $\phi \equiv_U \psi$，若 $\phi(x) = \psi(x)$（$\forall x \in U$）。等价地，$\phi\big|_U = \psi\big|_U$（域限制算子定义意义下的 $\mathcal{X}_{\mathrm{op}}$ 等式）。


<a id="oet-5bedef30d593a0bc"></a>

**引理 4.11（局部等价的受限矩阵一致性）**：若 $\phi \equiv_U \psi$，则：

**(i)** $\mathscr{L}(\phi)\big|_U = \mathscr{L}(\psi)\big|_U$。

**(ii)** $\mathscr{K}(\phi)\big|_U = \mathscr{K}(\psi)\big|_U$。

**(iii)** $\mathbf{N}(\phi)\big|_U = \mathbf{N}(\psi)\big|_U$。

**证明**：受限矩阵仅涉及 $U$ 内的点对。对所有 $x, y \in U$，$d_j(\phi(x), \phi(y)) = d_j(\psi(x), \psi(y))$，故所有 Lip/co-Lip/零化条件在 $U$ 上完全一致。$\square$


<a id="oet-11fd78baa402e538"></a>

**命题 4.12（局部等价不蕴含全域等价）**：若 $\mathcal X\setminus\{\bot\}$ 至少含有两个不同点，则存在定义域相同的算子 $\phi,\psi\in\mathcal X_{\mathrm{op}}$ 及非空子集 $U\subseteq\mathrm{dom}(\phi)$，使得 $\phi\equiv_U\psi$，但 $\phi\neq\psi$。

**证明**：取不同的非吸收点 $a,b$，令 $\phi=\mathrm{id}_{\mathcal X}$，并定义

$$
\psi(x)=
\begin{cases}
a,&x=b,\\
x,&x\neq b.
\end{cases}
$$

因 $b\neq\bot$，有 $\psi(\bot)=\bot$，故 $\psi\in\mathcal X_{\mathrm{op}}$。又因 $a\neq\bot$，$\psi$ 在每个非吸收点的输出均非吸收，所以

$$
\mathrm{dom}(\phi)=\mathrm{dom}(\psi)=\mathcal X\setminus\{\bot\}.
$$

取 $U=\{a\}$，则 $U$ 是共同定义域的非空子集。由 $a\neq b$，有 $\psi(a)=a=\phi(a)$，故 $\phi\equiv_U\psi$。但 $\phi(b)=b\neq a=\psi(b)$，所以 $\phi\neq\psi$。$\square$

> **注（局部等价的代数含义）**：[引理 4.11](<#user-content-oet-5bedef30d593a0bc>) 和 [命题 4.12](<#user-content-oet-11fd78baa402e538>) 共同表明：受限矩阵只读取算子在 $U$ 上的逐点行为，不携带 $U$ 外的信息。域限制保留 $\phi$ 在 $U$ 上的度量信息，同时丢弃域外行为。

在算子链中替换某一步时，只需比较两个算子在该步实际输入域上的作用。下面沿用 [§ 4.1](<#user-content-oet-5a1b95150c3a4df2>) 的实际输入域序列，说明这种替换如何保持整条链的结果。


<a id="oet-95e7f90e21e41cae"></a>

**命题 4.13（逐步局部等价保持复合结果）**：设两个 $k$-步链（$k\ge0$）

$$
c=(\phi_1,\ldots,\phi_k),\qquad c'=(\psi_1,\ldots,\psi_k)
$$

两条链的复合算子分别为

$$
c_k=\phi_k\circ\cdots\circ\phi_1,\qquad c'_k=\psi_k\circ\cdots\circ\psi_1,
$$

当 $k=0$ 时，两者均为 $\operatorname{id}_{\mathcal X}$。取非空初始集 $U_1\subseteq\operatorname{dom}(c_k)\cap\operatorname{dom}(c'_k)$。它们相对于 $U_1$ 的实际输入域序列分别为 $\{U_s\}_{s=1}^{k+1}$ 与 $\{V_s\}_{s=1}^{k+1}$，其中 $V_1=U_1$。若对所有 $s=1,\ldots,k$ 都有

$$
\phi_s \equiv_{U_s} \psi_s,
$$

则：

**(i)** 实际输入域序列一致：$U_s = V_s$（$1\le s\le k+1$）。

**(ii)** 链的复合行为在 $U_1$ 上局部等价：$c_k \equiv_{U_1} c'_k$。

**(iii)** 链的受限矩阵一致：$\mathscr{L}(c_k)\big|_{U_1} = \mathscr{L}(c'_k)\big|_{U_1}$，$\mathscr{K}(c_k)\big|_{U_1} = \mathscr{K}(c'_k)\big|_{U_1}$，$\mathbf{N}(c_k)\big|_{U_1} = \mathbf{N}(c'_k)\big|_{U_1}$。

**证明**：

**(i)** 对 $s$ 归纳。基础：$V_1 = U_1$（前提）。归纳步：设 $V_s = U_s$。因 $\phi_s \equiv_{U_s} \psi_s$：

$$
\phi_s(x) = \psi_s(x) \quad (\forall x \in U_s)
$$

故 $U_{s+1} = \phi_s(U_s) = \psi_s(U_s) = V_{s+1}$。

**(ii)** 对 $x\in U_1$，令 $x_0=x'_0=x$，并递归定义 $x_s=\phi_s(x_{s-1})$、$x'_s=\psi_s(x'_{s-1})$。若 $x_{s-1}=x'_{s-1}$，由 $x_{s-1}\in U_s$ 与第 $s$ 步的局部等价，得到 $x_s=x'_s$。归纳至 $s=k$，即得 $c_k(x)=c'_k(x)$；$k=0$ 时两边均为 $x$。

**(iii)** 由 (ii) 得 $c_k \equiv_{U_1} c'_k$，再由 [引理 4.11](<#user-content-oet-5bedef30d593a0bc>) 即得。$\square$

沿给定次序连续作用时，每一步的实际输入由初始输入与此前的作用共同决定。若再按输入所在的子域选择不同的后续作用，计算过程便同时具有复合与分支结构。下一章将引入算子网络，描述这些局域作用如何连接并共同确定计算结果。


<a id="oet-dfbba76d6c1273e3"></a>

### 4.6 习题


<div data-mb-exercise="oet-51ab39dbe6ea409d">

**习题 4.1（单步矩阵界与自复合）**：以下空间均补入吸收元，伪度量按吸收元隔离公理扩展，算子均保持吸收元。各矩阵界在相应的实数部分全域上考察。

**(i)** 在 $\mathbb R^2$ 上取

$$
d_1(x,y)=|x_1-y_1|,\qquad d_2(x,y)=|x_2-y_2|,
$$

令 $\phi(s,t)=(s+t,-s-t)$。求逐条目最小的 Lip 矩阵 $\mathbf L$，计算 $\rho(\mathbf L)$、$\mathbf L^n$ 与 $\phi^n$（$n\ge1$）。

**(ii)** 在 $\mathbb R$ 上取 $d(x,y)=|x-y|$，令 $\psi(x)=x+x^3$。求最大的单分量 co-Lip 证书及其谱半径，并对任意 $x\ne y$ 求

$$
\lim_{n\to\infty}|\psi^n(x)-\psi^n(y)|.
$$

</div>



<div data-mb-exercise="oet-0ff7986894ec9221">

**习题 4.2（长链中的有限步归零）**：设 $(\phi_m)_{m\ge1}\subseteq\mathcal X_{\mathrm{op}}$，取非空 $U_1$，递归定义 $U_{m+1}=\phi_m(U_m)$，并假设 $U_m\subseteq\operatorname{dom}(\phi_m)$ 对所有 $m\ge1$ 成立。对每个 $m$ 选取

$$
\mathbf L^{(m)}\in\mathscr L(\phi_m)\big|_{U_m},
$$

沿用有序乘积及空乘积约定。固定 $i^*,j^*\in I$ 与 $x,x'\in U_1$。若存在 $r^{\mathrm N}_0>0$ 与 $m_0\ge1$，使得对所有 $m\ge m_0$ 与所有 $y\in U_m$，

$$
r^{\mathrm N}_{\phi_m,i^*,j^*}(y\mid U_m)\ge r^{\mathrm N}_0,
$$

且

$$
\sum_{i\in I}\left[\overleftarrow{\prod}_{r=1}^{m-1}\mathbf L^{(r)}\right]_{i\to i^*}d_i(x,x')\to0,
$$

证明存在 $M\ge m_0$，使得对所有 $m\ge M$，

$$
d_{j^*}\bigl((\phi_m\circ\cdots\circ\phi_1)(x),(\phi_m\circ\cdots\circ\phi_1)(x')\bigr)=0.
$$

</div>



<div data-mb-exercise="oet-b7e77b504317782a">

**习题 4.3（一致正熵差下界给出的有限步熵归零）**：设 $c=(\phi_1,\ldots,\phi_k)$ 为长度 $k\in\mathbb N_0$ 的算子链，其复合算子为 $c_k=\phi_k\circ\cdots\circ\phi_1$，固定分量 $d_i\in\mathcal G$ 与 $\varepsilon\in(0,+\infty)$。令 $U_1=\operatorname{dom}(c_k)\ne\emptyset$、$U_{m+1}=\phi_m(U_m)$（$1\le m\le k$），并假设各 $U_m$ 非空、各步熵差均良定。

设初始熵有限，记 $e_1=E_{\varepsilon,i}(U_1)\in[0,+\infty)$。假设存在有限正数 $\delta$，使得对每个 $1\le m\le k$，只要 $E_{\varepsilon,i}(U_m)>0$，就有 $\Delta E_{\varepsilon,i}(\phi_m\mid U_m)\ge\delta$。

**(i)（有限熵前缀）** 设 $1\le r\le k$，且 $E_{\varepsilon,i}(U_m)>0$ 对 $1\le m\le r$ 均成立。证明 $U_1,\ldots,U_{r+1}$ 上的熵均为有限非负实数；记其值为 $e_m$，则

$$
e_{m+1}\le e_m-\delta\qquad(1\le m\le r).
$$

**(ii)（归零步数）** 令

$$
k^*:=\left\lceil\frac{e_1}{\delta}\right\rceil\in\mathbb N_0.
$$

证明：若 $k\ge k^*$，则存在 $1\le m\le k^*+1$ 使得 $E_{\varepsilon,i}(U_m)=0$。

</div>
