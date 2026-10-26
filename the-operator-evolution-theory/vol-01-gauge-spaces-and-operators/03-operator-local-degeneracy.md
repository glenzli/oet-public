
<a id="oet-5ee7bb37b515fb84"></a>

## 第 3 章 算子局部退化

算子可能使原本可区分的点在某些分量伪度量下变得不可区分。本章先用分量分划与计算纤维描述受限域上的局部退化，并通过纤维比较给出像值因子化的判据。随后用零化半径衡量纤维的局部范围，研究输入尺度与零化半径对像集覆盖数的约束，最后以映射熵差描述指定精度下输入、输出覆盖熵的变化。


<a id="oet-273361882c9d8ace"></a>

### 3.1 分量分划及其复合性质

为描述算子在给定子集上的局部行为，先根据各分量伪度量下的零距关系，对指标集作如下划分。

**定义（分量分划）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\mathcal G=\{d_i\}_{i\in I}$ 为给定规范结构，$U\subseteq\mathrm{dom}(\phi)$。依次定义：

- **常值分量**

$$
I_{\mathrm{const}}(\phi\mid U)=\{i\in I:\forall x,y\in U,\ d_i(\phi(x),\phi(y))=0\}.
$$

- **恒等分量**

$$
I_{\mathrm{id}}(\phi\mid U)=\{i\in I\setminus I_{\mathrm{const}}(\phi\mid U):\forall x\in U,\ d_i(\phi(x),x)=0\}.
$$

- **有效分量**

$$
I_{\mathrm{act}}(\phi\mid U)=I\setminus\bigl(I_{\mathrm{const}}(\phi\mid U)\cup I_{\mathrm{id}}(\phi\mid U)\bigr).
$$

上述分划采用常值优先：同时满足输出两两零距与输出、输入逐点零距条件的指标，归入常值分量。当 $U=\mathrm{dom}(\phi)$ 时，称为**全域分划**，并省略记号中的限制后缀 $\mid U$。

这些分量类型与前章的矩阵界有如下联系。


<a id="oet-176471fbe0cf6b8c"></a>

**命题 3.1（分量类型的矩阵约束）**：设 $\phi\in\mathcal{X}_{\mathrm{op}}$，$U\subseteq\mathrm{dom}(\phi)$，$i\in I$。

**(i)** 若 $i\in I_{\mathrm{const}}(\phi\mid U)$，则输出分量 $i$ 的 Lip 上界可取零行：对所有 $x,y\in U$，

$$
d_i(\phi(x),\phi(y))\le \sum_{k\in I}0\cdot d_k(x,y)=0.
$$

**(ii)** 若 $i\in I_{\mathrm{const}}(\phi\mid U)$ 且 $\mathbf K\in\mathscr K(\phi)\big|_U$，则对任意源分量 $k\in I$，只要存在 $x,y\in U$ 使 $d_k(x,y)>0$，必有

$$
K_{k\to i}=0.
$$

**(iii)** 若 $i\in I_{\mathrm{id}}(\phi\mid U)$，则

$$
d_i(\phi(x),\phi(y))=d_i(x,y)\qquad(\forall x,y\in U).
$$

**证明**：

**(i)** 常值分量条件给出左端恒为 $0$；右端为零行求和，亦为 $0$。

**(ii)** 由 $i\in I_{\mathrm{const}}(\phi\mid U)$，对任意 $x,y\in U$ 有 $d_i(\phi(x),\phi(y))=0$。若某 $k$ 与点对 $x,y$ 满足 $d_k(x,y)>0$，co-Lip 不等式给出

$$
0=d_i(\phi(x),\phi(y))\ge \sum_{\ell\in I}K_{\ell\to i}d_\ell(x,y)\ge K_{k\to i}d_k(x,y).
$$

由非负性与 $d_k(x,y)>0$ 得 $K_{k\to i}=0$。

**(iii)** 由 $i\in I_{\mathrm{id}}(\phi\mid U)$，对任意 $z\in U$ 有 $d_i(\phi(z),z)=0$。三角不等式给出

$$
d_i(\phi(x),\phi(y))\le d_i(\phi(x),x)+d_i(x,y)+d_i(y,\phi(y))=d_i(x,y),
$$

反向同理：

$$
d_i(x,y)\le d_i(x,\phi(x))+d_i(\phi(x),\phi(y))+d_i(\phi(y),y)=d_i(\phi(x),\phi(y)).
$$

合并即得等式。$\square$

下面考察分量分划 $(I_{\mathrm{const}}, I_{\mathrm{id}}, I_{\mathrm{act}})$ 在算子复合下的包含关系。



<a id="oet-e1615fa20ede09bc"></a>

**命题 3.2（复合下的有效分量包含与恒等分量保留）**：**(i)** 对于复合算子 $\phi_2 \circ \phi_1 \in \mathcal{X}_{\mathrm{op}}$，给定初始受限子集 $U \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$：
$$
I_{\mathrm{act}}(\phi_2 \circ \phi_1 \mid U) \;\subseteq\; I_{\mathrm{act}}(\phi_1 \mid U) \cup I_{\mathrm{act}}(\phi_2 \mid \phi_1(U))
$$

**(ii)** 对任意有限复合 $c_n = \phi_n \circ \cdots \circ \phi_1$，设 $U_1 \subseteq \mathrm{dom}(c_n)$，令 $U_{m+1} = \phi_m(U_m)$，则
$$
I_{\mathrm{act}}(c_n \mid U_1) \subseteq \bigcup_{m=1}^n I_{\mathrm{act}}(\phi_m \mid U_m)
$$
换言之，若对某个分量 $d_i$，全复合中每个单体算子在对应受限像集 $U_m$ 上均非有效，则复合算子在 $U_1$ 上也非有效。

**(iii) 恒等分量保留**：

$$
I_{\mathrm{id}}(\phi_1 \mid U) \cap I_{\mathrm{id}}(\phi_2 \mid \phi_1(U)) \;\subseteq\; I_{\mathrm{id}}(\phi_2 \circ \phi_1 \mid U).
$$

**证明**：

**(i)** 取逆否。设

$$
i \notin I_{\mathrm{act}}(\phi_1 \mid U) \cup I_{\mathrm{act}}(\phi_2 \mid \phi_1(U)).
$$

也就是说，$\phi_1$ 在 $U$ 上、$\phi_2$ 在像集 $\phi_1(U)$ 上各自为恒等或常值。需证

$$
i \notin I_{\mathrm{act}}(\phi_2 \circ \phi_1 \mid U).
$$

设 $x,y\in U$。分四种情况：

**(a)** $i \in I_{\mathrm{id}}(\phi_1 \mid U)$ 且 $i \in I_{\mathrm{id}}(\phi_2 \mid \phi_1(U))$：
$$
d_i((\phi_2 \circ \phi_1)(x), x) \leq d_i(\phi_2(\phi_1(x)), \phi_1(x)) + d_i(\phi_1(x), x) = 0 + 0 = 0
$$
又由 [命题 3.1](<#user-content-oet-176471fbe0cf6b8c>) 的恒等分量保距性质，对任意 $x,y\in U$，

$$
d_i(\phi_2(\phi_1(x)),\phi_2(\phi_1(y)))=d_i(\phi_1(x),\phi_1(y)).
$$

由于 $i\in I_{\mathrm{id}}(\phi_1\mid U)$ 已排除 $\phi_1$ 的输出两两零距，复合的输出也不可能两两零距。因此 $i\in I_{\mathrm{id}}(\phi_2\circ\phi_1\mid U)$。

**(b)** $i \in I_{\mathrm{id}}(\phi_1 \mid U)$ 且 $i \in I_{\mathrm{const}}(\phi_2 \mid \phi_1(U))$：
$$
d_i(\phi_2(\phi_1(x)), \phi_2(\phi_1(y))) = 0
$$
故 $i \notin I_{\mathrm{act}}(\phi_2 \circ \phi_1 \mid U)$。

**(c)** $i \in I_{\mathrm{const}}(\phi_1 \mid U)$ 且 $i \in I_{\mathrm{id}}(\phi_2 \mid \phi_1(U))$：
两次应用三角不等式得：
$$
d_i(\phi_2(\phi_1(x)), \phi_2(\phi_1(y))) \leq d_i(\phi_2(\phi_1(x)), \phi_1(x)) + d_i(\phi_1(x), \phi_1(y)) + d_i(\phi_1(y), \phi_2(\phi_1(y)))
$$
其中：$d_i(\phi_2(\phi_1(x)), \phi_1(x)) = 0$（由 $\phi_1(x) \in \phi_1(U)$ 及 $\phi_2$ 约束）；$d_i(\phi_1(x), \phi_1(y)) = 0$（由 $\phi_1$ 常值）；$d_i(\phi_1(y), \phi_2(\phi_1(y))) = 0$。
故 $i \notin I_{\mathrm{act}}(\phi_2 \circ \phi_1 \mid U)$。

**(d)** $i \in I_{\mathrm{const}}(\phi_1 \mid U)$ 且 $i \in I_{\mathrm{const}}(\phi_2 \mid \phi_1(U))$：
$$
d_i(\phi_2(\phi_1(x)), \phi_2(\phi_1(y))) = 0
$$
故 $i \notin I_{\mathrm{act}}(\phi_2 \circ \phi_1 \mid U)$。

**(ii)** 对复合长度归纳。空复合 $c_0$ 是恒等算子，其各分量均为常值或恒等，故 $I_{\mathrm{act}}(c_0\mid U_1)=\varnothing$，结论成立。

假设结论对长度 $n$ 成立。对 $c_{n+1}=\phi_{n+1}\circ c_n$，有 $U_1\subseteq\mathrm{dom}(c_n)$ 且 $U_{n+1}=c_n(U_1)$。由 (i) 及归纳假设，

$$
\begin{aligned}
I_{\mathrm{act}}(c_{n+1}\mid U_1)
&\subseteq I_{\mathrm{act}}(c_n\mid U_1)\cup I_{\mathrm{act}}(\phi_{n+1}\mid U_{n+1})\\
&\subseteq \bigcup_{m=1}^{n+1} I_{\mathrm{act}}(\phi_m\mid U_m).
\end{aligned}
$$

**(iii)** 设 $i$ 属于左侧交集。对所有 $x \in U$，由三角不等式公设：

$$
d_i(\phi_2(\phi_1(x)), x) \leq d_i(\phi_2(\phi_1(x)), \phi_1(x)) + d_i(\phi_1(x), x) = 0 + 0 = 0.
$$

结合 (i) 的情形 (a) 中排除常值分量的论证，得到 $i\in I_{\mathrm{id}}(\phi_2\circ\phi_1\mid U)$。$\square$


<a id="oet-8f36f69dab71e689"></a>

> **注（复合分量保持的逆向蕴含一般不成立）**：同一个两点换位例同时说明 [命题 3.2](<#user-content-oet-e1615fa20ede09bc>) 的 (i) 与 (iii) 一般不能反向：即使 $i \in I_{\mathrm{act}}(\phi_1 \mid U) \cap I_{\mathrm{act}}(\phi_2 \mid \phi_1(U))$，复合后也可能落入恒等分量；即使 $\phi_1,\phi_2$ 在各自受限域上均不属于 $d_i$-恒等分量，复合也可能属于 $d_i$-恒等分量。
>
> **证明**：取 $\mathcal X=\{\bot,a,b\}$，$U=\{a,b\}$，规范结构只有一个分量 $d_i$。令
>
> $$
> d_i(a,b)=d_i(b,a)=1,\qquad d_i(x,x)=0\quad(x\in\mathcal X),
> $$
>
> 并令吸收元与其余各点之间的距离为 $+\infty$。
>
> 令 $\phi_1,\phi_2$ 都保持吸收元，并定义
>
> $$
> \phi_1(a)=\phi_2(a)=b,\qquad \phi_1(b)=\phi_2(b)=a.
> $$
>
> 于是 $\phi_1(U)=U$，两步均在同一子集 $U$ 上考察。
>
> 对 $r=1,2$，有
>
> $$
> d_i(\phi_r(a),\phi_r(b))=d_i(b,a)=1,
> $$
>
> 故 $i$ 不是常值分量；又有
>
> $$
> d_i(\phi_r(a),a)=d_i(b,a)=1,
> $$
>
> 故 $i$ 也不是恒等分量。因此，两步均满足
>
> $$
> I_{\mathrm{act}}(\phi_r\mid U)=\{i\},\qquad I_{\mathrm{id}}(\phi_r\mid U)=\varnothing.
> $$
>
> 复合算子则将 $a,b$ 分别映回自身，且两个输出之间的距离仍为 $1$，所以
>
> $$
> I_{\mathrm{id}}(\phi_2\circ\phi_1\mid U)=\{i\},\qquad I_{\mathrm{act}}(\phi_2\circ\phi_1\mid U)=\varnothing.
> $$
>
> 因此，[命题 3.2](<#user-content-oet-e1615fa20ede09bc>) 的 (i) 中，右侧为 $\{i\}$，左侧为空集；(iii) 中，右侧为 $\{i\}$，左侧为空集。两条包含关系在此均为严格包含，反向包含都不成立。$\square$


<a id="oet-2c5dc85febaac657"></a>

**命题 3.3（常值分量的单侧保持与非封闭性）**：设子集 $U \subseteq \mathrm{dom}(\psi \circ \phi)$。常值分量集合 $I_{\mathrm{const}}$ 在复合映射中满足以下单侧规律：

**(i) 外侧常值保持**：若外侧算子在内侧的像集上属于常值分量，则复合算子在同一分量上也属于常值分量：

$$
i\in I_{\mathrm{const}}(\psi\mid\phi(U))\implies i\in I_{\mathrm{const}}(\psi\circ\phi\mid U).
$$

**(ii) 内侧常值未必保持**：若内侧算子在 $U$ 上退化，由于外侧算子可能区分内侧输出中同分量零距的点，复合算子一般不继承该特征：
$$
i \in I_{\mathrm{const}}(\phi \mid U) \nRightarrow i \in I_{\mathrm{const}}(\psi \circ \phi \mid U)
$$
若外侧算子的相应输出上界仅包含同一输入分量，则可以保持内侧的常值退化，见 [推论 3.4](<#user-content-oet-87c593824d28aa93>)。

**证明**：
**(i)** 条件 $i \in I_{\mathrm{const}}(\psi \mid \phi(U))$ 蕴含：对任意 $z_1, z_2 \in \phi(U)$，恒有 $d_i(\psi(z_1), \psi(z_2)) = 0$。令 $z_1 = \phi(x), z_2 = \phi(y)$，其中 $x, y \in U$，代入即得

$$
d_i((\psi \circ \phi)(x),(\psi \circ \phi)(y))=0\qquad(\forall x,y\in U).
$$

由常值分量定义即得 $i\in I_{\mathrm{const}}(\psi\circ\phi\mid U)$。

**(ii)** 反例：取 $\mathcal X=\{\bot,a,b,p,q,r,s\}$，$I=\{i,m\}$。对 $k\in I$，令

$$
d_k(x,x)=0\quad(x\in\mathcal X),\qquad d_k(\bot,x)=d_k(x,\bot)=+\infty\quad(x\ne\bot).
$$

在非吸收元部分，令 $d_i(p,q)=d_i(q,p)=0$，其余不同点之间的 $d_i$-距离均为 $1$；令 $d_m$ 为不同点之间距离为 $1$ 的离散度量。$d_i$ 将 $p,q$ 合为一个零距类，并在不同零距类之间取距离 $1$，故这两个分量均满足扩展伪度量公理。

取 $U=\{a,b\}$，定义 $\phi(a)=p$、$\phi(b)=q$、$\psi(p)=r$、$\psi(q)=s$，两个算子在其余点均取值 $\bot$。则：
- $d_i(\phi(a), \phi(b)) = d_i(p,q) = 0$，故 $i \in I_{\mathrm{const}}(\phi \mid U)$；
- $(\psi \circ \phi)(a) = r$，$(\psi \circ \phi)(b) = s$，$d_i(r, s) = 1 > 0$，故 $i \notin I_{\mathrm{const}}(\psi \circ \phi \mid U)$。

这里 $\phi(U)$ 在 $d_m$ 下可分辨（$d_m(p,q) = 1$），而复合输出在 $d_i$ 下亦可分辨。$\square$



<a id="oet-87c593824d28aa93"></a>

**推论 3.4（常值分量在复合中的保持条件）**：设 $c=\psi\circ\phi$，$U\subseteq\mathrm{dom}(c)$。若 $j\in I_{\mathrm{const}}(\phi\mid U)$，且存在 $\mathbf L\in\mathscr L(\psi)\big|_{\phi(U)}$ 满足 $L_{k\to j}=0$ 对所有 $k\ne j$ 成立，则

$$
j\in I_{\mathrm{const}}(\psi\circ\phi\mid U).
$$

**证明**：由所选 Lip 矩阵第 $j$ 行的零项条件，对任意 $x,y\in U$ 有

$$
d_j(\psi(\phi(x)),\psi(\phi(y)))\le L_{j\to j}\,d_j(\phi(x),\phi(y))=0.
$$

其中末项由 $j\in I_{\mathrm{const}}(\phi\mid U)$ 得到。故复合输出在 $d_j$ 下两两零距，按定义属于常值分量。$\square$


<a id="oet-77b9589cc080d4f0"></a>

### 3.2 计算纤维与像值因子化

给定算子、受限子集与规范子族，我们考察所有输出与指定目标点零距的输入点。本节将这样的输入点集合称为计算纤维，先讨论其基本性质，再通过纤维分划的比较判断像值因子化何时存在。

下文使用 [§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>) 中的子族复合伪度量 $d_J$。条件 $d_J(x,y)=0$ 意味着 $x$ 与 $y$ 在子族 $J$ 的每一个分量伪度量下均不可区分。

#### 定义（计算纤维）

设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$y \in \mathcal X$。给定定义域的子集 $U \subseteq \mathrm{dom}(\phi)$，并指定非空指标集子族 $J \subseteq I$。定义 $y$ 在 $\phi$ 下关于规范子族 $\mathcal{G}_J$ 在受限区域 $U$ 内的**计算纤维**：

$$
\operatorname{Fib}_{\phi, J}(y \mid U) := \bigl\{x \in U \;\big|\; d_J(\phi(x), y) = 0\bigr\}
$$

即子集 $U$ 内所有在复合伪度量 $d_J$ 下被映射等价至 $y$ 的点集合。定义允许任意目标 $y\in\mathcal X$；当 $y$ 与 $\phi(U)$ 中每一点都具有正 $d_J$-距离时，相应纤维为空。取 $y\in\phi(U)$，并将相同纤维去重，便得到下述分划。当区域放宽至全域 $U = \mathrm{dom}(\phi)$ 时，省略限制尾缀记作 $\operatorname{Fib}_{\phi, J}(y)$。

单分量情形下记作 $\operatorname{Fib}_{\phi, j}(y \mid U)$。


<a id="oet-8d9c504286a147a3"></a>

**命题 3.5（计算纤维的基本性质）**：设 $U \subseteq \mathrm{dom}(\phi)$，$J,K \subseteq I$ 均非空。则：

**(i) 目标零距不变性**：若 $d_J(y,y')=0$，则
$$
\operatorname{Fib}_{\phi,J}(y\mid U)=\operatorname{Fib}_{\phi,J}(y'\mid U).
$$

**(ii) 纤维分划**：将相同纤维去重，所得集合族
$$
\{\operatorname{Fib}_{\phi,J}(y\mid U):y\in\phi(U)\}
$$
构成 $U$ 的分划。也就是说，这些纤维覆盖 $U$，并且对任意 $y_1,y_2\in\phi(U)$，对应纤维要么相等，要么不交。

**(iii) 分量交集律**：
$$
\operatorname{Fib}_{\phi,J}(y\mid U)
=\bigcap_{j\in J}\operatorname{Fib}_{\phi,j}(y\mid U).
$$

**(iv) 子族单调性**：若 $J\subseteq K$，则
$$
\operatorname{Fib}_{\phi,K}(y\mid U)
\subseteq
\operatorname{Fib}_{\phi,J}(y\mid U).
$$

**(v) 子族边界**：当 $J=\{i\}$ 时，
$$
\operatorname{Fib}_{\phi,J}(y\mid U)
=\operatorname{Fib}_{\phi,i}(y\mid U)
=\{x\in U:d_i(\phi(x),y)=0\};
$$
当 $J=I$ 时，
$$
\operatorname{Fib}_{\phi,I}(y\mid U)\subseteq \operatorname{Fib}_{\phi,i}(y\mid U)\qquad(i\in I).
$$

**(vi) 分量分划边界**：当 $J=\{j\}$ 时，若 $j \in I_{\mathrm{id}}(\phi \mid U)$，则
$$
\operatorname{Fib}_{\phi,j}(y\mid U)=\{x\in U:d_j(x,y)=0\}.
$$
若 $j \in I_{\mathrm{const}}(\phi \mid U)$，任取 $y_0\in\phi(U)$，则
$$
\operatorname{Fib}_{\phi,j}(y_0\mid U)=U;
$$
并且当 $d_j(y,y_0)>0$ 时，
$$
\operatorname{Fib}_{\phi,j}(y\mid U)=\emptyset.
$$

因此，恒等分量与常值分量分别给出上述两类极端纤维。仅凭分量分划本身，不再对有效分量 $j \in I_{\mathrm{act}}(\phi \mid U)$ 的纤维形态作进一步分类。

**证明**：若 $x\in\operatorname{Fib}_{\phi,J}(y\mid U)$ 且 $d_J(y,y')=0$，则对每个 $j\in J$，有
$$
d_j(\phi(x),y)=0,\qquad d_j(y,y')=0.
$$
由三角不等式得 $d_j(\phi(x),y')=0$。反向由对称性同理，故 (i) 成立。

对任意 $x\in U$，取 $y=\phi(x)\in\phi(U)$，由自距为零得 $x\in\operatorname{Fib}_{\phi,J}(y\mid U)$，故这些纤维覆盖 $U$。若两个纤维有交点 $x$，则由纤维定义与对称性，对每个 $j\in J$，
$$
d_j(y_1,y_2)\le d_j(y_1,\phi(x))+d_j(\phi(x),y_2)=0.
$$
于是 $d_J(y_1,y_2)=0$，由 (i) 得两个纤维相等；否则二者不交。每个以 $\phi(U)$ 中的点为目标的纤维均非空，因此去重后得到 $U$ 的分划。

(iii) 由 $d_J=\max_{j\in J}d_j$ 直接得到：$d_J(\phi(x),y)=0$ 当且仅当所有 $d_j(\phi(x),y)=0$ 同时成立。若 $J\subseteq K$，则 $K$-纤维要求更多分量同时零距，故包含于 $J$-纤维，得到 (iv)。

(v) 的单分量等式是 $J=\{i\}$ 代入定义；当 $J=I$ 时，全纤维要求所有 $d_i(\phi(x),y)$ 同时为零，故它包含于任一单分量纤维。

(vi) 的恒等分量情形由 $d_j(\phi(x),x)=0$ 与三角不等式双向传递零距离，得到

$$
d_j(\phi(x),y)=0\iff d_j(x,y)=0.
$$

常值分量情形中，若 $y_0\in\phi(U)$，则任意 $x\in U$ 均满足 $d_j(\phi(x),y_0)=0$，故纤维为 $U$。

若 $d_j(y,y_0)>0$，则任意 $x\in U$ 都不可能同时满足

$$
d_j(\phi(x),y)=0,\qquad d_j(\phi(x),y_0)=0,
$$

否则三角不等式给出 $d_j(y,y_0)=0$。$\square$



#### 纤维比较与像值因子化

计算纤维记录哪些输入的输出不可区分。比较两个算子的纤维分划，还可以判断一个算子的像值能否经映射得到另一个算子的像值。这里需要区分点值相等与族零距：沿用 [引理 1.1](<01-foundations.md#user-content-oet-ecdfb943b4fb8922>) 的关系 $\sim_{\mathcal G}$，对 $U\subseteq\operatorname{dom}(\phi)$ 记

$$
\mathcal R_{=}(\phi\mid U)=\{(x,y)\in U\times U:\phi(x)=\phi(y)\},
$$

$$
\mathcal R_{\sim}(\phi\mid U)=\{(x,y)\in U\times U:\phi(x)\sim_{\mathcal G}\phi(y)\}.
$$

第二类点对集正是计算纤维的关系表达：对 $x,y\in U$，

$$
(x,y)\in\mathcal R_{\sim}(\phi\mid U)
\quad\Longleftrightarrow\quad
y\in\operatorname{Fib}_{\phi,I}(\phi(x)\mid U).
$$


<a id="oet-6d303a1afa732703"></a>

**命题 3.6（像值因子化与标量 Lip 界）**：设 $\phi_A,\phi_B\in\mathcal X_{\mathrm{op}}$，$U\subseteq\operatorname{dom}(\phi_A,\phi_B)$。考虑满足 $T\circ\phi_A=\phi_B$（在 $U$ 上）的映射 $T:\phi_A(U)\to\mathcal X$。

**(i)** 这样的 $T$ 存在，当且仅当

$$
\mathcal R_{=}(\phi_A\mid U)\subseteq\mathcal R_{=}(\phi_B\mid U).
$$

**(ii)** 两个方向的像值变换都存在，当且仅当

$$
\mathcal R_{=}(\phi_A\mid U)=\mathcal R_{=}(\phi_B\mid U).
$$

**(iii)** 在单分量情形下，若 $T$ 存在，且存在有限标量 $K_A>0$、$L_B\geq0$，使 $\phi_A$ 在 $U$ 上为 $K_A$-co-Lip、$\phi_B$ 在 $U$ 上为 $L_B$-Lip，则 $T$ 在 $\phi_A(U)$ 上为 $(L_B/K_A)$-Lip。

**证明**：若 $T$ 存在，则 $\phi_A(x)=\phi_A(y)$ 蕴含

$$
\phi_B(x)=T(\phi_A(x))=T(\phi_A(y))=\phi_B(y),
$$

得到 (i) 的必要性。反之，按 $T(\phi_A(x))=\phi_B(x)$ 赋值。若同一像点有两个代表元，所给包含关系保证赋值相同，故 $T$ 良定义。对两个方向分别应用 (i)，即得 (ii)。

对 (iii)，任取 $y,y'\in\phi_A(U)$，选取代表元 $x,x'\in U$，使 $y=\phi_A(x)$、$y'=\phi_A(x')$。由 co-Lip 下界和 $K_A>0$，

$$
d(x,x')\leq K_A^{-1}d(y,y').
$$

再用 $\phi_B$ 的 Lip 上界，得到

$$
d(T(y),T(y'))=d(\phi_B(x),\phi_B(x'))
\leq L_Bd(x,x')\leq\frac{L_B}{K_A}d(y,y').
$$

因此所需标量 Lip 界成立。$\square$


<a id="oet-c21391963ef67ef0"></a>

**命题 3.7（零距商上的像值因子化）**：设 $\phi_A,\phi_B\in\mathcal X_{\mathrm{op}}$，并任取 $U\subseteq\mathrm{dom}(\phi_A,\phi_B)$。沿用上述族零距关系 $\sim_{\mathcal G}$。

存在满足规定赋值公式

$$
\overline T:\phi_A(U)/{\sim_{\mathcal G}}\longrightarrow\phi_B(U)/{\sim_{\mathcal G}},
\qquad
\overline T([\phi_A(x)])=[\phi_B(x)]\quad(x\in U)
$$

的商映射，当且仅当

$$
\mathcal R_{\sim}(\phi_A\mid U)\subseteq\mathcal R_{\sim}(\phi_B\mid U).
$$

按上述赋值公式诱导的双向商变换存在，当且仅当
$$
\mathcal R_{\sim}(\phi_A\mid U)=\mathcal R_{\sim}(\phi_B\mid U).
$$

若规范族分别在两个像集 $\phi_A(U)$ 与 $\phi_B(U)$ 上分离，即在各自像集内，全分量零距都蕴含点相等，则

$$
\mathcal R_{=}(\phi_A\mid U)=\mathcal R_{\sim}(\phi_A\mid U),
\qquad
\mathcal R_{=}(\phi_B\mid U)=\mathcal R_{\sim}(\phi_B\mid U).
$$

在此前提下，单向点值变换判据与单向商值变换判据等价，双向点值变换判据与双向商值变换判据也等价。

**证明**：由 [引理 1.1](<01-foundations.md#user-content-oet-ecdfb943b4fb8922>)，族零距关系限制到两个像集后仍为等价关系，故商集有定义。

若点对集包含成立，则 $\phi_A(x)\sim_{\mathcal G}\phi_A(y)$ 蕴含 $\phi_B(x)\sim_{\mathcal G}\phi_B(y)$。因此按所列公式赋值不依赖代表元，得到商映射。

反之，若存在满足该公式的商映射，则对任何 $\phi_A(x)\sim_{\mathcal G}\phi_A(y)$，有

$$
[\phi_B(x)]
=\overline T([\phi_A(x)])
=\overline T([\phi_A(y)])
=[\phi_B(y)].
$$

于是 $\phi_B(x)\sim_{\mathcal G}\phi_B(y)$，给出所需包含。对两个方向分别应用这一等价条件，即得双向判据。

对 $\phi_A$ 与 $\phi_B$ 分别考察点对集。点值相等由自距为零推出全分量零测距，故 $\mathcal R_{=}\subseteq\mathcal R_{\sim}$。反向包含分别使用规范族在相应像集上的分离性。因此两个像集都分离时，两侧各自的 $\mathcal R_{=}$ 与 $\mathcal R_{\sim}$ 相等；把这两个等式代入单向包含判据与双向等式判据，即得两类判据的一致性。$\square$

**定义（零测距纤维预序 $\succeq_{\mathrm{fiber},U}$）**：设 $\phi_A,\phi_B\in\mathcal X_{\mathrm{op}}$，$U\subseteq\operatorname{dom}(\phi_A,\phi_B)$。若

$$
\mathcal R_{\sim}(\phi_A\mid U)\subseteq\mathcal R_{\sim}(\phi_B\mid U),
$$

则记 $\phi_A\succeq_{\mathrm{fiber},U}\phi_B$，称 $\phi_A$ 在 $U$ 上的零测距纤维不低于 $\phi_B$。这表示 $\phi_A$ 的零测距纤维分划细于或等于 $\phi_B$ 的相应分划；由 [命题 3.7](<#user-content-oet-c21391963ef67ef0>)，也等价于存在按对应输入诱导的商映射。当 $U$ 固定时，简写为 $\phi_A\succeq_{\mathrm{fiber}}\phi_B$。


<a id="oet-b99ec286d2be8e72"></a>

> **注（纤维包含的传递）**：上述关系具有自反性与传递性，因而是预序。若 $\phi_0,\ldots,\phi_m$ 具有公共评估域 $U$，且 $\phi_{r-1}\succeq_{\mathrm{fiber},U}\phi_r$ 对每一步成立，则对任意 $0\leq a<b\leq m$ 都有 $\phi_a\succeq_{\mathrm{fiber},U}\phi_b$。若整条链中某一步零测距点对集的包含为真包含，则 $\mathcal R_{\sim}(\phi_0\mid U)\subsetneq\mathcal R_{\sim}(\phi_m\mid U)$。
>
> **证明**：自反性与传递性分别来自集合包含的自反性与传递性。记 $R_k=\mathcal R_{\sim}(\phi_k\mid U)$（$0\leq k\leq m$）。对任意 $0\leq a<b\leq m$，逐步包含给出
>
> $$
> R_a\subseteq R_{a+1}\subseteq\cdots\subseteq R_b,
> $$
>
> 即 $\phi_a\succeq_{\mathrm{fiber},U}\phi_b$。若某个 $1\leq r\leq m$ 满足 $R_{r-1}\subsetneq R_r$，则可取
>
> $$
> (x,y)\in R_r\setminus R_{r-1}\subseteq R_m\setminus R_0,
> $$
>
> 其中差集包含由 $R_0\subseteq R_{r-1}$ 与 $R_r\subseteq R_m$ 得到。结合 $R_0\subseteq R_m$，即得 $R_0\subsetneq R_m$。$\square$


<a id="oet-bb1487a09d8bf151"></a>

### 3.3 零化半径与零化矩阵

纤维比较描述不同算子所给分划的粗细。下面进一步考察单个计算纤维在基点附近的距离范围，为此引入零化内切半径与零化矩阵。

#### 定义（零化内切半径）

设 $\phi \in \mathcal{X}_{\mathrm{op}}$。选取非空子集 $U \subseteq \mathrm{dom}(\phi)$ 作为评估域，并取基点 $y \in U$。给定 $\mathcal{X}$ 上的扩展伪度量 $d_{\mathrm{in}},d_{\mathrm{out}}$，记

$$
B_{d_{\mathrm{in}}}(y,r) := \{x\in\mathcal{X}:d_{\mathrm{in}}(x,y)<r\}.
$$

在 $U$ 上，关于输入伪度量 $d_{\mathrm{in}}$ 与输出伪度量 $d_{\mathrm{out}}$ 定义算子在该点的**零化内切半径**：

$$
r^{\mathrm N}_{\phi, d_{\mathrm{in}}, d_{\mathrm{out}}}(y \mid U) := \sup\bigl\{r \in (0, +\infty) \;\big|\; B_{d_{\mathrm{in}}}(y, r) \cap U \subseteq \{x\in U:d_{\mathrm{out}}(\phi(x),\phi(y))=0\}\bigr\}
$$

记号中的直立上标 $\mathrm N$ 是零化标签，不表示幂。其中 $r \in (0, +\infty)$，约定 $\sup \emptyset = 0$：若不存在任何有限正半径使开球包含于输出零测距集合，则零化半径为零。$r^{\mathrm N}$ 本身可取值 $+\infty$（当任意大的有限半径开球均满足包含条件时）。

当输出伪度量取子族复合伪度量 $d_{\mathrm{out}}=d_J$ 时，右侧输出零测距集合就是计算纤维 $\operatorname{Fib}_{\phi,J}(\phi(y)\mid U)$。因此对非空 $J\subseteq I$ 约定简写：

$$
r^{\mathrm N}_{\phi,i,J}(y\mid U) := r^{\mathrm N}_{\phi,d_i,d_J}(y\mid U).
$$

对于单输出分量 $J=\{j\}$，进一步简记为 $r^{\mathrm N}_{\phi,i,j}(y\mid U)=r^{\mathrm N}_{\phi,d_i,d_j}(y\mid U)$。

当 $U=\mathrm{dom}(\phi)$ 时，简记为 $r^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(y)$。分量情形下，严格小于该半径的输入距离所满足的零距判据见 [命题 3.11](<#user-content-oet-70882b889ff4ec94>)；距离恰等于该半径时，定义不作保证。

为获得对一组基点统一适用的零化尺度，下面固定评估域，对这些基点的零化内切半径取下确界。

#### 定义（统一零化半径）

设 $\phi\in\mathcal X_{\mathrm{op}}$，$\emptyset\neq A\subseteq U\subseteq\operatorname{dom}(\phi)$，并给定输入、输出扩展伪度量 $d_{\mathrm{in}},d_{\mathrm{out}}$。定义基点集合 $A$ 关于评估域 $U$ 的**统一零化半径**为

$$
\underline{r}^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(A\mid U)
:=\inf_{y\in A}r^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(y\mid U).
$$

这里，$U$ 限定开球的评估范围 $B_{d_{\mathrm{in}}}(y,r)\cap U$，$A$ 指定取下确界的基点集合。当 $A=U$ 时，简记为

$$
\underline{r}^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}\big|_U
:=\underline{r}^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(U\mid U)
=\inf_{y\in U}r^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}(y\mid U).
$$

输入、输出指标沿用点态半径的简写规则。当 $A=U=\operatorname{dom}(\phi)$ 时，进一步简记为 $\underline{r}^{\mathrm N}_{\phi,d_{\mathrm{in}},d_{\mathrm{out}}}$。


<a id="oet-ae07c4b78c2b63cd"></a>

**反例 3.1（处处正的零化半径未必有正的统一下界）**：取 $\mathcal X=\mathbb R\sqcup\{\bot\}$，仅设一个距离分量 $d_1=d$：实数部分使用通常距离，$\bot$ 与实数点的距离为 $+\infty$，且 $d(\bot,\bot)=0$。定义

$$
f(x)=
\begin{cases}
0,&x<0,\\
1,&x\geq0,
\end{cases}
\qquad f(\bot)=\bot,
\qquad U=[-1,0)\cup(0,1].
$$

则对每个 $y\in U$，

$$
r^{\mathrm N}_{f,d,d}(y\mid U)=|y|>0,
\qquad
\underline{r}^{\mathrm N}_{f,d,d}\big|_U=0.
$$

**证明**：当 $0<r\leq|y|$ 时，$B_d(y,r)\cap U$ 中的点均与 $y$ 同号，故输出相同。当 $r>|y|$ 时，可在 $U$ 中取一个与 $y$ 异号、充分接近零的点 $x$，使 $d(x,y)<r$，而 $d(f(x),f(y))=1$。因此合法半径恰为 $(0,|y|]$，零化半径为 $|y|$。由于 $U$ 内的点可任意接近零，对基点取下确界即得统一半径为 $0$。$\square$

每个基点各自有一个正的零化尺度，并不保证存在对所有基点共同适用的正尺度。后文的零化阈值与覆盖数约束需要的正是后一种保证。

#### 定义（零化矩阵）

取基点集合 $A=U$，将各单分量的统一零化半径排列为矩阵。定义算子 $\phi\in\mathcal X_{\mathrm{op}}$ 在非空子集 $U\subseteq\operatorname{dom}(\phi)$ 上的**零化矩阵** $\mathbf{N}(\phi)\big|_U\in\bar{\mathbb R}_+^{|I|\times|I|}$：

$$
[\mathbf{N}(\phi)\big|_U]_{ji} := \underline{r}^{\mathrm N}_{\phi, i, j}\big|_U
$$

该矩阵以输出分量 $j \in I$ 为行指标，以输入分量 $i \in I$ 为列指标。全定义域情形 $U = \mathrm{dom}(\phi)$ 下，记为**全域零化矩阵** $\mathbf{N}(\phi)$。

> **约定**：本章涉及 $\underline{r}^{\mathrm N}$ 或 $\mathbf{N}(\phi)\big|_U$ 时，默认 $U \neq \emptyset$。


<a id="oet-fd32966bed4ea8d0"></a>

**命题 3.8（常值分量与统一零化半径）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\emptyset\neq U\subseteq\operatorname{dom}(\phi)$，$\emptyset\neq J\subseteq I$。则：

**(i)** 若 $J\subseteq I_{\mathrm{const}}(\phi\mid U)$，则对任意基点 $y\in U$ 有

$$
\operatorname{Fib}_{\phi,J}(\phi(y)\mid U)=U,
$$

且对任意输入指标 $i\in I$ 有

$$
\underline{r}^{\mathrm N}_{\phi,i,J}\big|_U=+\infty.
$$

**(ii)** 对指标 $i,j\in I$，条件 $[\mathbf N(\phi)\big|_U]_{ji}=+\infty$ 一般不能推出 $j\in I_{\mathrm{const}}(\phi\mid U)$。

**证明**：

**(i)** 任取 $y\in U$。由常值条件，对任意 $x\in U$ 与 $j\in J$ 均有

$$
d_j(\phi(x),\phi(y))=0,
$$

故 $\operatorname{Fib}_{\phi,J}(\phi(y)\mid U)=U$。于是，对任意输入指标 $i\in I$，每个有限正半径开球 $B_i(y,r)\cap U$ 都包含于该纤维，因而

$$
r^{\mathrm N}_{\phi,i,J}(y\mid U)=+\infty.
$$

再对 $y\in U$ 取下确界，即得 $\underline{r}^{\mathrm N}_{\phi,i,J}\big|_U=+\infty$。

这里的 $+\infty$ 指合法半径参数没有有限上界。即使 $U$ 在 $d_i$ 下有界，开球覆盖 $U$ 后仍可继续增大半径，而交集 $B_i(y,r)\cap U$ 不再变化。这既不要求 $U$ 内存在任意大的偏离距离，也不涉及 $U$ 外的点。

**(ii)** 取 $\mathcal X=\{\bot,a,b\}$，$U=\{a,b\}$，各分量自距为 $0$，并令 $\bot$ 与非吸收元在每个分量下距离为 $+\infty$。

若 $i=j$，取 $d_i(a,b)=+\infty$；若 $i\neq j$，取

$$
d_i(a,b)=+\infty,\qquad d_j(a,b)=1.
$$

其余分量任取满足扩展伪度量公理并隔离 $\bot$ 的取值。取 $\phi=\mathrm{id}_{\mathcal X}$。

对任意基点 $y\in U$，任意有限正半径开球 $B_i(y,r)\cap U$ 只含 $y$，因而包含于 $\operatorname{Fib}_{\phi,j}(\phi(y)\mid U)$。所以

$$
r^{\mathrm N}_{\phi,i,j}(y\mid U)=+\infty,
$$

从而 $[\mathbf N(\phi)\big|_U]_{ji}=+\infty$。另一方面，$d_j(\phi(a),\phi(b))>0$，故 $j\notin I_{\mathrm{const}}(\phi\mid U)$。$\square$


<a id="oet-ff54b8d36fa86c90"></a>

**命题 3.9（恒等分量的纤维与零化半径）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$y\in U\subseteq\operatorname{dom}(\phi)$，且 $i\in I_{\mathrm{id}}(\phi\mid U)$。则：

**(i)** 以 $\phi(y)$ 为目标的计算纤维等于 $y$ 在 $U$ 内的输入零距类：

$$
\operatorname{Fib}_{\phi,i}(\phi(y)\mid U)=\{x\in U:d_i(x,y)=0\}.
$$

**(ii)** 若有限正半径 $r_0$ 满足

$$
B_i(y,r_0)\cap U\subseteq\{x\in U:d_i(x,y)=0\},
$$

则

$$
r^{\mathrm N}_{\phi,i,i}(y\mid U)\ge r_0>0.
$$

**证明**：

**(i)** 由 [命题 3.1](<#user-content-oet-176471fbe0cf6b8c>)(iii)，对任意 $x\in U$ 有

$$
d_i(\phi(x),\phi(y))=d_i(x,y).
$$

左端为零当且仅当右端为零，代入计算纤维定义即得所述等式。

**(ii)** 由 (i) 与开球包含条件，

$$
B_i(y,r_0)\cap U\subseteq\operatorname{Fib}_{\phi,i}(\phi(y)\mid U).
$$

因此 $r_0$ 是零化内切半径定义中的合法半径，故 $r^{\mathrm N}_{\phi,i,i}(y\mid U)\ge r_0>0$。$\square$

> **注（零化内切球的局部性）**：内切球 $B_i(y, r) \cap U$ 只记录围绕基点 $y$ 的局部纤维包含。零化半径不记录该开球之外的纤维成员。


<a id="oet-2b53c51151014456"></a>

**命题 3.10（统一零化半径的分量最小值公式）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\emptyset\neq U\subseteq\operatorname{dom}(\phi)$，$i\in I$，且 $J,K\subseteq I$ 均非空。则

$$
\underline{r}^{\mathrm N}_{\phi, i, J}\big|_U \;=\; \min_{j \in J} \, [\mathbf{N}(\phi)\big|_U]_{ji}
$$

并且当 $J\subseteq K$ 时，

$$
\underline{r}^{\mathrm N}_{\phi,i,K}\big|_U
\le
\underline{r}^{\mathrm N}_{\phi,i,J}\big|_U.
$$

**证明**：固定 $y\in U$。由 [命题 3.5](<#user-content-oet-8d9c504286a147a3>) 的分量交集律，半径 $r$ 对目标子族 $J$ 合法，当且仅当它对每个 $j\in J$ 的单分量纤维均合法。各合法半径集关于减小半径向下封闭；由于 $J$ 有限非空，故

$$
r^{\mathrm N}_{\phi,i,J}(y\mid U)
=
\min_{j\in J}r^{\mathrm N}_{\phi,i,j}(y\mid U).
$$

再对 $y\in U$ 取下确界。有限非空最小值与该下确界满足

$$
\inf_{y\in U}\min_{j\in J}a_{y,j}
=
\min_{j\in J}\inf_{y\in U}a_{y,j},
$$

因而得到第一式。若 $J\subseteq K$，则对更多指标取最小值不会增大，第二式随即成立。$\square$

纤维截断是单步零化现象：若两个输入点已经落入同一计算纤维，或二者距离落入该算子的零化半径内，则该步输出在相应分量上零测距。


<a id="oet-70882b889ff4ec94"></a>

**命题 3.11（纤维截断的单步判据）**：设 $\phi_2\in\mathcal X_{\mathrm{op}}$，$U_2\subseteq\operatorname{dom}(\phi_2)$，$i,j\in I$，且 $y,y'\in U_2$。若

$$
y'\in\operatorname{Fib}_{\phi_2,j}\bigl(\phi_2(y)\mid U_2\bigr)
$$

或

$$
d_i(y,y')<r^{\mathrm N}_{\phi_2,i,j}(y\mid U_2),
$$

则

$$
d_j(\phi_2(y),\phi_2(y'))=0.
$$

特别地，若 $\phi_1 \in \mathcal{X}_{\mathrm{op}}$，$x, x' \in \mathrm{dom}(\phi_1)$，$\phi_1(x), \phi_1(x') \in U_2$，且

$$
\phi_1(x') \in \operatorname{Fib}_{\phi_2, j}\bigl(\phi_2(\phi_1(x)) \mid U_2\bigr),
$$

则

$$
d_j\bigl((\phi_2 \circ \phi_1)(x),(\phi_2 \circ \phi_1)(x')\bigr)=0.
$$

**证明**：第一个条件由计算纤维定义给出 $d_j(\phi_2(y'),\phi_2(y))=0$，再由对称性即得结论。

若第二个条件成立，由零化半径的上确界定义，存在有限正半径 $\rho>d_i(y,y')$，使得

$$
B_i(y,\rho)\cap U_2\subseteq\operatorname{Fib}_{\phi_2,j}\bigl(\phi_2(y)\mid U_2\bigr).
$$

由对称性与 $y'\in U_2$ 得 $y'\in B_i(y,\rho)\cap U_2$，故归结为第一个条件。复合情形取 $y=\phi_1(x)$、$y'=\phi_1(x')$ 即得。$\square$


<a id="oet-1217d1061a2c95ce"></a>

**命题 3.12（统一零化半径的复合下界）**：设 $\phi_1,\phi_2\in\mathcal X_{\mathrm{op}}$，$\phi=\phi_2\circ\phi_1$，$\emptyset\neq U\subseteq\mathrm{dom}(\phi)$，固定 $i,j,l\in I$。

**(i) 零距保持下的传播**：若对所有 $y,y'\in\phi_1(U)$，

$$
d_l(y,y')=0\quad\Longrightarrow\quad d_j(\phi_2(y),\phi_2(y'))=0,
$$

则

$$
[\mathbf N(\phi)\big|_U]_{ji}\ge [\mathbf N(\phi_1)\big|_U]_{li}.
$$

**(ii) 经 Lip 上界拉回**：若存在 $0<L<+\infty$，使得对所有 $x,x'\in U$，

$$
d_l(\phi_1(x),\phi_1(x'))\le L\,d_i(x,x'),
$$

则

$$
[\mathbf N(\phi)\big|_U]_{ji}\ge
\frac{[\mathbf N(\phi_2)\big|_{\phi_1(U)}]_{jl}}{L}.
$$

**证明**：分别记两项右侧的下界为 $M_1$、$M_2$。对任意 $x,x'\in U$：

**(i)** 若 $d_i(x,x')<M_1$，则该距离严格小于 $\phi_1$ 在基点 $x$ 处相应的零化半径。由 [命题 3.11](<#user-content-oet-70882b889ff4ec94>) 得 $d_l(\phi_1(x),\phi_1(x'))=0$，再由零距保持条件得 $d_j(\phi(x),\phi(x'))=0$。

**(ii)** 若 $d_i(x,x')<M_2$，由 $0<L<+\infty$ 及 Lip 上界，

$$
d_l(\phi_1(x),\phi_1(x'))
\le L\,d_i(x,x')
< [\mathbf N(\phi_2)\big|_{\phi_1(U)}]_{jl}.
$$

对 $\phi_2$ 应用 [命题 3.11](<#user-content-oet-70882b889ff4ec94>)，同样得到 $d_j(\phi(x),\phi(x'))=0$。

两种情形下，对每个基点 $x\in U$，任意满足 $0<r<M_s$ 的有限半径都使 $B_i(x,r)\cap U$ 包含于相应计算纤维（$s=1,2$）。由零化半径的上确界定义，再对基点取下确界，即得所需不等式；$M_s=0$ 时结论由非负性直接成立。$\square$

> **注（三类受限矩阵）**：在评估域 $U$ 上，选定的 $\mathbf L\in\mathscr L(\phi)\big|_U$ 与 $\mathbf K\in\mathscr K(\phi)\big|_U$ 分别给出分量距离的上界与下界；$\mathbf N(\phi)\big|_U$ 的条目则由零化半径确定，记录各输入、输出分量之间的局部零距尺度。


<a id="oet-83287e414000b50b"></a>

### 3.4 输入尺度与零化阈值

统一零化半径给出输入距离足够小时输出零距的判据。反例 [反例 3.1](<#user-content-oet-ae07c4b78c2b63cd>) 表明，即使各点半径都为正，统一半径仍可能低于任意正阈值。为比较统一零化半径与输入域本身的大小，先固定输入尺度函数与两个阈值。

**定义（输入尺度函数族）**：一族映射

$$
\sigma_i:\{A\subseteq\mathcal{X}:A\neq\emptyset\}\to\bar{\mathbb{R}}_+\qquad(i\in I)
$$

称为输入尺度函数族，若对任意非空子集 $A_1,A_2\subseteq\mathcal X$ 满足

$$
A_1\subseteq A_2\Rightarrow\sigma_i(A_1)\leq\sigma_i(A_2)\qquad(i\in I).
$$

若无额外说明，默认取直径尺度

$$
\sigma_i(A)=\mathrm{diam}_{d_i}(A)=\sup_{x,y\in A}d_i(x,y).
$$

取两个有限正阈值

$$
0<\tau_\sigma<+\infty,\qquad 0<\tau_{\mathrm N}<+\infty.
$$

其中 $\tau_\sigma$ 用于比较输入域的尺度，$\tau_{\mathrm N}$ 用于比较算子在输入域上的统一零化半径。

**定义（阈值分类）**：设 $f\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne A\subseteq\operatorname{dom}(f)$。对通道 $(i,j)\in I^2$，定义

$$
\operatorname{Type}_{f,A}(i,j)
=
\left(
\mathbf 1_{\{\sigma_i(A)<\tau_\sigma\}},
\mathbf 1_{\{\underline{r}^{\mathrm N}_{f,i,j}\big|_A\geq\tau_{\mathrm N}\}}
\right)
\in\{0,1\}^2,
$$

其中 $\mathbf 1_{\{P\}}$ 在条件 $P$ 成立时取 $1$，否则取 $0$。第一项只依赖输入分量 $i$，记录输入域的尺度；第二项依赖通道 $(i,j)$，记录该域上统一零化半径与阈值的比较。两个判断的组合如下：

| 输入域的尺度 | $\underline{r}^{\mathrm N}_{f,i,j}\big\vert_A\geq\tau_{\mathrm N}$ | $\underline{r}^{\mathrm N}_{f,i,j}\big\vert_A<\tau_{\mathrm N}$ |
| --- | --- | --- |
| $\sigma_i(A)<\tau_\sigma$ | $(1,1)$ | $(1,0)$ |
| $\sigma_i(A)\geq\tau_\sigma$ | $(0,1)$ | $(0,0)$ |

$\operatorname{Type}_{f,A}$ 记录所选尺度函数族与阈值下的局部形态；改变算子、评估域或阈值，都可能改变分类。


<a id="oet-76dc176ee249f20a"></a>

**引理 3.13（两项阈值分类及其单调性）**：固定 $f$、$A$、输入尺度函数族及两个阈值后，每个通道 $(i,j)$ 恰落入上述四种组合之一。并且：

**(i)** 固定其他数据，若 $\tau_\sigma$ 增大，则第一项取 $1$ 的通道集合单调不减。

**(ii)** 固定其他数据，若 $\tau_{\mathrm N}$ 增大，则第二项取 $1$ 的通道集合单调不增。

**证明**：两项判断各由互补的两个不等式给出，故四种组合互斥且穷尽。若 $\tau_\sigma\leq\tau'_\sigma$、$\tau_{\mathrm N}\leq\tau'_{\mathrm N}$，则

$$
\sigma_i(A)<\tau_\sigma
\Rightarrow\sigma_i(A)<\tau'_\sigma,
\qquad
\underline{r}^{\mathrm N}_{f,i,j}\big|_A\geq\tau'_{\mathrm N}
\Rightarrow\underline{r}^{\mathrm N}_{f,i,j}\big|_A\geq\tau_{\mathrm N}.
$$

这分别给出两项单调性。$\square$

固定算子与阈值后，输入域的加细具有下面的单调性。


<a id="oet-451ca2134cd62db4"></a>

**命题 3.14（域缩小下的尺度与统一零化半径单调性）**：设 $f\in\mathcal X_{\mathrm{op}}$，且

$$
\varnothing\ne B\subseteq A\subseteq\operatorname{dom}(f).
$$

则：

**(i)** 对任意输入分量 $i$，有 $\sigma_i(B)\leq\sigma_i(A)$。特别地，若 $\sigma_i(A)<\tau_\sigma$，则 $\sigma_i(B)<\tau_\sigma$。

**(ii)** 对任意通道 $(i,j)$，统一零化半径满足

$$
\underline{r}^{\mathrm N}_{f,i,j}\big|_B
\geq
\underline{r}^{\mathrm N}_{f,i,j}\big|_A.
$$

**(iii)** 反向尺度判断一般不成立：可能有 $\sigma_i(B)<\tau_\sigma$，但 $\sigma_i(A)\geq\tau_\sigma$。

**证明**：

**(i)** 由 $B\subseteq A$ 与输入尺度函数族的单调性，得 $\sigma_i(B)\leq\sigma_i(A)$；阈值结论随即成立。

**(ii)** 固定 $x\in B$。在 $A$ 上使开球落入同一计算纤维的每个有限正半径，在 $B$ 上仍满足这一条件，故

$$
r^{\mathrm N}_{f,i,j}(x\mid B)\geq r^{\mathrm N}_{f,i,j}(x\mid A).
$$

于是

$$
\inf_{x\in B}r^{\mathrm N}_{f,i,j}(x\mid B)
\geq\inf_{x\in B}r^{\mathrm N}_{f,i,j}(x\mid A)
\geq\inf_{x\in A}r^{\mathrm N}_{f,i,j}(x\mid A).
$$

**(iii)** 在带吸收元的实直线上采用通常距离，取 $f=\operatorname{id}_{\mathcal X}$、$A=\{0,1\}$、$B=\{0\}$。采用直径尺度，并取 $\tau_\sigma=1/2$，则 $\sigma(B)=0<\tau_\sigma$，而 $\sigma(A)=1\geq\tau_\sigma$。$\square$


<a id="oet-9a382b889145a3a6"></a>

### 3.5 局部零化与覆盖数

统一零化半径先给出输出可分离点对所需的输入距离，再把输入覆盖转化为输出覆盖。若非空输入域在某个输入分量上的直径严格小于该域上相应通道的统一零化半径，则域内全部点对的输出在相应输出分量下零距，像集便只需一个覆盖中心。


<a id="oet-6ad76403c3bfeb84"></a>

**命题 3.15（统一零化半径给出的分离阈值）**：设 $f\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne A\subseteq\operatorname{dom}(f)$，并固定通道 $(i,j)\in I^2$。记

$$
\underline{r}^{\mathrm N}=\underline{r}^{\mathrm N}_{f,i,j}\big|_{A}.
$$

则：

**(i)（低于统一零化半径必归零）** 对任意 $x,y\in A$，若

$$
d_i(x,y)<\underline{r}^{\mathrm N},
$$

则

$$
d_j(f(x),f(y))=0.
$$

**(ii)（输出正分离时的输入距离下界）** 对任意 $x,y\in A$，若

$$
d_j(f(x),f(y))>0,
$$

则

$$
d_i(x,y)\geq \underline{r}^{\mathrm N}.
$$

**(iii)（零化半径不足时的分离见证）** 若 $\underline{r}^{\mathrm N}<\tau_{\mathrm N}$，则对任意有限正数 $\alpha$ 满足

$$
\underline{r}^{\mathrm N}<\alpha<\tau_{\mathrm N},
$$

存在 $x,y\in A$ 与有限正数 $\varepsilon$，使得

$$
d_i(x,y)<\alpha,
$$

且

$$
\varepsilon\le d_j(f(x),f(y)).
$$

**证明**：

**(i)** 若 $d_i(x,y)<\underline{r}^{\mathrm N}$，则由统一零化半径的定义，

$$
d_i(x,y)<\underline{r}^{\mathrm N}
=\inf_{z\in A}r^{\mathrm N}_{f,i,j}(z\mid A)
\leq r^{\mathrm N}_{f,i,j}(x\mid A).
$$

由 [命题 3.11](<#user-content-oet-70882b889ff4ec94>) 的单步判据，得 $d_j(f(x),f(y))=0$。

**(ii)** 是 (i) 的逆否命题。

**(iii)** 取有限正数 $\alpha$ 满足 $\underline{r}^{\mathrm N}<\alpha<\tau_{\mathrm N}$。由下确界定义，存在 $y\in A$ 使

$$
r^{\mathrm N}_{f,i,j}(y\mid A)<\alpha.
$$

若 $B_i(y,\alpha)\cap A$ 全部包含于 $\operatorname{Fib}_{f,j}(f(y)\mid A)$，则 $\alpha$ 是 $y$ 处零化半径定义中的可取半径，推出

$$
\alpha\leq r^{\mathrm N}_{f,i,j}(y\mid A),
$$

矛盾。因此存在 $x\in B_i(y,\alpha)\cap A$ 使

$$
d_j(f(x),f(y))>0.
$$

由于 $d_j(f(x),f(y))>0$，可取有限正数 $\varepsilon$ 使

$$
0<\varepsilon\leq d_j(f(x),f(y)).
$$

若右侧为 $+\infty$，取任意有限正数即可；若右侧有限，则取不超过它的有限正数。$\square$


<a id="oet-9ecc7d0b4b541992"></a>

**命题 3.16（零化阈值下的纤维包含与覆盖数约束）**：设 $f\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne A\subseteq\operatorname{dom}(f)$，并固定通道 $(i,j)\in I^2$。取有限正阈值 $\tau_{\mathrm N}$。若 $\underline{r}^{\mathrm N}_{f,i,j}\big|_A\geq\tau_{\mathrm N}$，则：

**(i)（纤维包含）** 对任意 $x\in A$，

$$
B_i(x,\tau_{\mathrm N})\cap A
\subseteq
\operatorname{Fib}_{f,j}(f(x)\mid A).
$$

**(ii)（子集的覆盖数与熵约束）** 对任意 $B\subseteq A$ 与任意 $\varepsilon\in(0,+\infty)$，

$$
\mathcal{N}_j\bigl(\varepsilon,f(B)\bigr)
\leq
\mathcal{N}_i(\tau_{\mathrm N},B).
$$

当 $B\neq\emptyset$ 时，由度量熵定义（[§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>)），等价地，

$$
E_{\varepsilon,j}(f(B))\leq E_{\tau_{\mathrm N},i}(B).
$$

**证明**：

**(i)** 若 $y\in B_i(x,\tau_{\mathrm N})\cap A$，则

$$
d_i(x,y)<\tau_{\mathrm N}\leq\underline{r}^{\mathrm N}_{f,i,j}\big|_A.
$$

由 [命题 3.15](<#user-content-oet-6ad76403c3bfeb84>)(i)，$d_j(f(x),f(y))=0$，即得纤维包含。

**(ii)** 若 $B=\emptyset$，两侧覆盖数均为 $0$。以下设 $B\ne\emptyset$。任取 $B$ 的一个有限 $\tau_{\mathrm N}$-内覆盖中心集 $S\subseteq B$。对任意 $a\in B$，存在 $s\in S$ 使

$$
d_i(a,s)<\tau_{\mathrm N}.
$$

由 (i)，$d_j(f(a),f(s))=0$。故 $f(B)$ 中每个点都与 $f(S)$ 中某个点在 $d_j$ 下零距，因此 $f(S)$ 是任意 $\varepsilon\in(0,+\infty)$ 下的内覆盖；并且 $|f(S)|\le |S|$。因此输出覆盖数不超过每个可取的输入中心数。再对全部有限 $\tau_{\mathrm N}$-内覆盖取下确界，得到覆盖数不等式；若输入不存在有限内覆盖，右端为 $+\infty$，不等式仍成立。熵不等式由 $\log_2$ 的单调性得到。$\square$

在反例 [反例 3.1](<#user-content-oet-ae07c4b78c2b63cd>) 中，这个统一阈值条件不能替换为“每点零化半径均为正”。事实上，对任意有限正数 $\tau$，取 $0<a\leq1$ 且 $2a<\tau$，令 $B=\{-a,a\}\subset U$。输入两点可由一个内部中心在半径 $\tau$ 下覆盖，而 $f(B)=\{0,1\}$ 在半径 $1/2$ 下需要两个内部中心，故

$$
\mathcal N_1(\tau,B)=1<2=\mathcal N_1\bigl(1/2,f(B)\bigr).
$$

这里 $B$ 随 $\tau$ 选取；它说明，仅有固定评估域 $U$ 上的点态正半径，不能保证存在一个正的输入尺度，使上述覆盖数不等式对所有 $B\subseteq U$ 同时成立。


<a id="oet-610f439b6ff59f79"></a>

**推论 3.17（小输入域上的整体零化判据）**：设 $f\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne A\subseteq\operatorname{dom}(f)$，并固定通道 $(i,j)\in I^2$。采用直径尺度，取两个有限正阈值 $\tau_\sigma,\tau_{\mathrm N}$，并设

$$
\operatorname{diam}_{d_i}(A)<\tau_\sigma\leq\tau_{\mathrm N}.
$$

则

$$
\underline{r}^{\mathrm N}_{f,i,j}\big|_A\geq\tau_{\mathrm N}
\quad\Longleftrightarrow\quad
\forall x,y\in A,\quad d_j(f(x),f(y))=0.
$$

当上述等价条件成立时，对任意 $\varepsilon\in(0,+\infty)$，

$$
\mathcal N_j(\varepsilon,f(A))=1.
$$

**证明**：若 $\underline{r}^{\mathrm N}_{f,i,j}\big|_A\geq\tau_{\mathrm N}$，则对任意 $x,y\in A$，

$$
d_i(x,y)\leq\operatorname{diam}_{d_i}(A)
<\tau_\sigma\leq\tau_{\mathrm N}\leq\underline{r}^{\mathrm N}_{f,i,j}\big|_A.
$$

由 [命题 3.15](<#user-content-oet-6ad76403c3bfeb84>)(i) 得 $d_j(f(x),f(y))=0$。反之，若所有输出点对均为 $d_j$-零距，则每个基点的全部有限正半径都满足受限域内的零化条件，故 $\underline{r}^{\mathrm N}_{f,i,j}\big|_A=+\infty\geq\tau_{\mathrm N}$。

$A$ 非空，故 $f(A)$ 也非空。任选其中一点作中心，其任意有限正半径的 $d_j$-球都覆盖整个像域；空中心集不能覆盖非空集合，因此覆盖数恰为 $1$。$\square$

在该推论的直径与阈值条件下，阈值分类 $\operatorname{Type}_{f,A}(i,j)$ 的第一项为 $1$，第二项恰好判断整个局部像是否落入同一个 $d_j$-零距类。这里的零距不要求输出点值相等。


<a id="oet-cf9f43f2f47eb03e"></a>

### 3.6 映射熵差


上一节直接比较输入与输出的覆盖数。固定精度以及两端的规范子族后，对覆盖数取对数便得到相应的度量熵（[§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>)）。本节将源集 $U$ 与像集 $\phi(U)$ 的度量熵之差称为**映射熵差**，用它描述所选规范与尺度下覆盖熵的变化。

#### 定义（映射熵差）

使用 [§ 1.2](<01-foundations.md#user-content-oet-65d0745eb743dfe2>) 中的子族度量熵。指定非空子集 $U \subseteq \mathrm{dom}(\phi)$、非空输入端子族 $\emptyset\neq J_{\mathrm{in}}\subseteq I$、非空输出端子族 $\emptyset\neq J_{\mathrm{out}}\subseteq I$ 及有限正精度 $\varepsilon\in(0,+\infty)$。在

$$
\mathcal N_{J_{\mathrm{in}}}(\varepsilon,U)<+\infty
\qquad\text{或}\qquad
\mathcal N_{J_{\mathrm{out}}}\bigl(\varepsilon,\phi(U)\bigr)<+\infty
$$

至少一个成立时，定义

$$
\Delta E_{\varepsilon,J_{\mathrm{in}},J_{\mathrm{out}}}(\phi\mid U)
:=
E_{\varepsilon,J_{\mathrm{in}}}(U)
-
E_{\varepsilon,J_{\mathrm{out}}}\bigl(\phi(U)\bigr)
\in [-\infty,+\infty].
$$

映射熵差取值于扩展实数 $\overline{\mathbb{R}} = [-\infty, +\infty]$，其中 $E_{\varepsilon,\cdot} \in [0, +\infty]$。当两个熵均有限时 $\Delta E$ 为普通实数。形式上：$E_{\varepsilon,J_{\mathrm{in}}}(U) = +\infty$ 且 $E_{\varepsilon,J_{\mathrm{out}}}(\phi(U)) < +\infty$ 时 $\Delta E = +\infty$；$E_{\varepsilon,J_{\mathrm{in}}}(U) < +\infty$ 且 $E_{\varepsilon,J_{\mathrm{out}}}(\phi(U)) = +\infty$ 时 $\Delta E = -\infty$。定义前提排除了两个熵同时为 $+\infty$ 的不定形。

当 $J_{\mathrm{in}}=J_{\mathrm{out}}=J$ 时简记为 $\Delta E_{\varepsilon,J}(\phi\mid U)$。本节仅按覆盖熵的变化解释其符号：$\Delta E>0$ 表示输出覆盖熵较小，$\Delta E<0$ 表示输出覆盖熵较大，$\Delta E=0$ 表示两端覆盖熵相同。


<a id="oet-f4a4cb93f576325e"></a>

> **注（有限集上映射熵差的良定性）**：若 $\emptyset\neq U\subseteq\mathrm{dom}(\phi)$ 为有限集，则对任意非空子族 $J_{\mathrm{in}},J_{\mathrm{out}}\subseteq I$ 与任意有限正精度 $\varepsilon$，$E_{\varepsilon,J_{\mathrm{in}}}(U)$ 与 $E_{\varepsilon,J_{\mathrm{out}}}(\phi(U))$ 均为有限实数，因而 $\Delta E_{\varepsilon,J_{\mathrm{in}},J_{\mathrm{out}}}(\phi\mid U)$ 良定。
>
> **证明**：有限集 $U$ 可由自身作为有限中心集覆盖，故
>
> $$
> \mathcal N_{J_{\mathrm{in}}}(\varepsilon,U)\le |U|<+\infty.
> $$
>
> $\phi(U)$ 也是非空有限集，同理
>
> $$
> \mathcal N_{J_{\mathrm{out}}}(\varepsilon,\phi(U))<+\infty.
> $$
>
> 两个覆盖数均为正有限整数，因此对应对数为有限实数，差值良定。$\square$

> **注（$\varepsilon$ 作为探测尺度）**：在本节定义中，$\varepsilon$ 只出现在覆盖数与度量熵中；计算纤维则由严格等式 $d_J(\phi(x), y) = 0$ 定义。


<a id="oet-56e96ed2cda64242"></a>

**命题 3.18（分量分划与映射熵差）**：设 $\emptyset\neq U\subseteq\mathrm{dom}(\phi)$，$\varepsilon\in(0,+\infty)$，$j\in I$。

**(i)** 若 $j\in I_{\mathrm{const}}(\phi\mid U)$，则

$$
\mathcal N_j(\varepsilon,\phi(U))=1,\qquad E_{\varepsilon,j}(\phi(U))=0,
$$

因此 $\Delta E_{\varepsilon,j}(\phi\mid U)=E_{\varepsilon,j}(U)$。

**(ii)** 若 $j\in I_{\mathrm{id}}(\phi\mid U)$，则

$$
\mathcal N_j(\varepsilon,\phi(U))=\mathcal N_j(\varepsilon,U),\qquad E_{\varepsilon,j}(\phi(U))=E_{\varepsilon,j}(U).
$$

因此只要 $\Delta E_{\varepsilon,j}(\phi\mid U)$ 良定，就有 $\Delta E_{\varepsilon,j}(\phi\mid U)=0$。

**证明**：

**(i)** 由于 $U$ 非空，$\phi(U)$ 非空。取任意 $y_0\in\phi(U)$。常值分量条件给出任意 $y\in\phi(U)$ 均满足

$$
d_j(y,y_0)=0<\varepsilon.
$$

故 $\{y_0\}$ 覆盖 $\phi(U)$；非空集合覆盖数不能为 $0$，所以覆盖数为 $1$，熵为 $\log_2 1=0$。

**(ii)** 由 [命题 3.1](<#user-content-oet-176471fbe0cf6b8c>) 的 (iii) 可知

$$
d_j(\phi(x),\phi(y))=d_j(x,y)\qquad(x,y\in U).
$$

若 $S\subseteq U$ 是 $U$ 的一个有限 $\varepsilon$-覆盖，则 $\phi(S)$ 是 $\phi(U)$ 的有限 $\varepsilon$-覆盖，故

$$
\mathcal N_j(\varepsilon,\phi(U))\le\mathcal N_j(\varepsilon,U).
$$

反向地，若 $T\subseteq\phi(U)$ 是 $\phi(U)$ 的有限 $\varepsilon$-覆盖，对每个 $t\in T$ 选取 $s_t\in U$ 使 $\phi(s_t)=t$。则 $\{s_t:t\in T\}$ 覆盖 $U$，故

$$
\mathcal N_j(\varepsilon,U)\le\mathcal N_j(\varepsilon,\phi(U)).
$$

两边合并得到覆盖数相等，熵相等。$\square$


<a id="oet-5f1e227b06f3a2d1"></a>

**命题 3.19（单通道 Lip 上界与熵差下界）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\emptyset\neq U\subseteq\operatorname{dom}(\phi)$，$i,j\in I$，且 $U$ 在 $d_i$ 下全有界（$\mathcal{N}_i(r,U)<\infty$，$\forall r\in(0,+\infty)$）。固定 $\varepsilon\in(0,+\infty)$。

若 $L\in(0,+\infty)$ 满足

$$
d_j(\phi(x),\phi(y))\le L\,d_i(x,y)
\qquad(\forall x,y\in U),
$$

则映射熵差良定且满足

$$
\Delta E_{\varepsilon,i,j}(\phi\mid U)
\geq
E_{\varepsilon,i}(U)-E_{\varepsilon/L,i}(U).
$$

**证明**：由假设，若 $x,c\in U$ 且 $d_i(x,c)<\varepsilon/L$，则

$$
d_j(\phi(x),\phi(c))\le L\,d_i(x,c)<\varepsilon.
$$

因此，$U$ 的任意有限 $\varepsilon/L$-$d_i$-内覆盖，其中心的像给出 $\phi(U)$ 的 $\varepsilon$-$d_j$-内覆盖，且中心数不增加，故

$$
\mathcal N_j(\varepsilon,\phi(U))
\leq\mathcal N_i(\varepsilon/L,U).
$$

由 $U$ 全有界，$\mathcal N_i(\varepsilon,U)$ 与右侧覆盖数均有限，从而像集的覆盖数也有限。又因 $U$ 非空，这些覆盖数均不小于 $1$，故相应度量熵均为有限实数，映射熵差良定。对覆盖数不等式取对数，再从 $E_{\varepsilon,i}(U)$ 中相减，即得结论。$\square$


<a id="oet-9d16603c422d3b11"></a>

**命题 3.20（co-Lip 常数与熵差上界）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\emptyset\neq U\subseteq\operatorname{dom}(\phi)$，$i,j\in I$，$\varepsilon\in(0,+\infty)$。若 $U$ 在 $d_i$ 下全有界，且存在 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 满足 $0<K_{i\to j}<+\infty$，则：

$$
\Delta E_{\varepsilon, i, j}(\phi \mid U) \;\leq\; E_{\varepsilon, i}(U) - E_{\varepsilon / K_{i\to j},\, i}(U)
$$

**证明**：
由 $0<K_{i\to j}<+\infty$，精度 $\varepsilon/K_{i\to j}$ 有限且为正。

对每个构成像集 $\phi(U)$ 的有限 $\varepsilon$-内覆盖中心集 $T\subseteq\phi(U)$，对每个 $t\in T$ 选取 $c_t\in U$ 使 $\phi(c_t)=t$，并记 $S=\{c_t:t\in T\}$。则 $S\subseteq U$、$|S|\le |T|$。对任意 $x\in U$，存在 $t\in T$ 使 $d_j(\phi(x),t)<\varepsilon$；取相应的 $c_t$，即有 $d_j(\phi(x),\phi(c_t))<\varepsilon$。

由 co-Lip 下界的定义（[§ 2.1](<02-operator-bounds.md#user-content-oet-af85899693cc8750>)）：对任意 $x, y \in U$，

$$
d_j(\phi(x),\phi(y))
\geq
\sum_{k \in I}K_{k \to j}d_k(x,y).
$$

co-Lip 矩阵元素 $K_{k \to j} \geq 0$，故求和的每一项非负，单项不超过全和：

$$
K_{i \to j}d_i(x,c_t)
\leq
\sum_{k \in I}K_{k \to j}d_k(x,c_t)
\leq
d_j(\phi(x),\phi(c_t))
<\varepsilon.
$$
由 $K_{i\to j}>0$ 两侧除以 $K_{i\to j}$，得到 $d_i(x,c_t)<\varepsilon/K_{i\to j}$。因此 $S$ 构成 $U$ 在 $d_i$ 下的有限 $\varepsilon/K_{i\to j}$-内覆盖，并且

$$
\mathcal{N}_i\bigl(\varepsilon/K_{i\to j},U\bigr)
\leq
|S|
\leq
|T|.
$$

对所有有限 $\varepsilon$-内覆盖中心集 $T$ 的基数 $|T|$ 取下确界；若不存在这样的 $T$，则该下确界按约定为 $+\infty$。两种情形统一得到

$$
\mathcal{N}_i\bigl(\varepsilon/K_{i\to j},U\bigr)
\leq
\mathcal{N}_j\bigl(\varepsilon,\phi(U)\bigr).
$$

取对数得 $E_{\varepsilon/K_{i\to j},i}(U)\leq E_{\varepsilon,j}(\phi(U))$。由于 $U$ 在 $d_i$ 下全有界，输入熵 $E_{\varepsilon,i}(U)$ 与 $E_{\varepsilon/K_{i\to j},i}(U)$ 均有限；即使输出熵为 $+\infty$，熵差也仍良定。代入 $\Delta E=E_{\varepsilon,i}(U)-E_{\varepsilon,j}(\phi(U))$ 即得。$\square$

计算纤维描述哪些输入在输出端不可区分，其比较给出像值因子化的判据；零化半径与输入尺度则进一步给出局部像的覆盖数与熵约束。当多个算子依次作用时，这些量须在逐步产生的实际像域上读取。下一章将研究这种复合过程中的距离与零距传播，并将各步映射熵差汇总为链的熵递推等式。


<a id="oet-4f189d7cb3bf58f9"></a>

### 3.7 习题


<div data-mb-exercise="oet-5a431d16f9d7ba6a">

**习题 3.1（计算纤维与自复合）**：取 $\mathcal X=\mathbb R\sqcup\{\bot\}$，规范结构只有一个分量 $d_i$，在实数部分定义

$$
d_i(x,y)=\bigl||x|-|y|\bigr|,
$$

并按吸收元约定扩展至 $\mathcal X$。令算子 $\phi$ 保持吸收元，且对 $x\in\mathbb R$ 定义

$$
\phi(x)=2x-1.
$$

取 $U=\{0,1\}$。

**(i)** 分别求

$$
\operatorname{Fib}_{\phi,i}(\phi(0)\mid U),
\qquad
\operatorname{Fib}_{\phi^2,i}(\phi^2(0)\mid U),
$$

并判定 $i$ 在 $\phi\mid U$ 与 $\phi^2\mid U$ 的分量分划中属于哪一类。

**(ii)** 若将 $\phi$ 换成在 $U$ 上取同一个实数值的算子，自复合后还能使 $0,1$ 落入不同的计算纤维吗？说明理由。

</div>



<div data-mb-exercise="oet-092ba6f495b988c1">

**习题 3.2（零化半径与距离间隙）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$\varnothing\ne U\subseteq\mathrm{dom}(\phi)$。在 $U$ 上选定 co-Lip 矩阵 $\mathbf K\in\mathscr K(\phi)\big|_U$，固定通道 $(i,j)$，并假设 $K_{i\to j}>0$。

**(i)** 固定 $y\in U$。若 $r^{\mathrm N}_{\phi,i,j}(y\mid U)>0$，证明对任意 $x\in U$ 都有

$$
d_i(x,y)\notin\bigl(0,r^{\mathrm N}_{\phi,i,j}(y\mid U)\bigr).
$$

**(ii)** 若 $\underline{r}^{\mathrm N}_{\phi,i,j}\big|_U>0$，证明对任意 $x,y\in U$ 都有

$$
d_i(x,y)\in\{0\}\sqcup\bigl[\underline{r}^{\mathrm N}_{\phi,i,j}\big|_U,+\infty\bigr].
$$

</div>



<div data-mb-exercise="oet-fc424fbae1afcbdc">

**习题 3.3（平移下的纤维与熵差）**：取 $\mathcal X=\mathbb R\sqcup\{\bot\}$，规范结构只有一个分量 $d_i$，在实数部分定义

$$
d_i(x,y)=\bigl||x|-|y|\bigr|,
$$

并按吸收元约定扩展至 $\mathcal X$。令 $\phi(\bot)=\bot$，且对 $x\in\mathbb R$ 定义 $\phi(x)=x+1$。取

$$
U=\{-3,-2,0,2\}.
$$

**(i)** 分别求恒等算子与 $\phi$ 关于 $d_i$ 在 $U$ 上的计算纤维分划。

**(ii)** 取 $\varepsilon=\tfrac32$，计算 $\mathcal N_i(\varepsilon,U)$、$\mathcal N_i(\varepsilon,\phi(U))$ 与 $\Delta E_{\varepsilon,i}(\phi\mid U)$。

</div>



<div data-mb-exercise="oet-7ade05e895653cab">

**习题 3.4（输入域改变下的阈值分类）**：取 $\mathcal X=\mathbb R\sqcup\{\bot\}$，实数部分采用通常距离 $d$，$\bot$ 与每个实数的距离为 $+\infty$。定义

$$
f(x)=\lfloor x\rfloor\quad(x\in\mathbb R),\qquad f(\bot)=\bot.
$$

取直径尺度与 $\tau_\sigma=\tau_{\mathrm N}=1$。

**(i)** 对下列四个局部输入域，分别计算 $\operatorname{diam}_d(D)$、$\underline{r}^{\mathrm N}_{f,d,d}\big\vert_D$，并确定对应的阈值组合：

$$
D=[0,\tfrac12],\qquad
D=[\tfrac9{10},\tfrac{11}{10}],\qquad
D=\{0,2\},\qquad
D=[0,2].
$$

**(ii)** 对任意非空 $D\subseteq\mathbb R$，是否都有

$$
\underline{r}^{\mathrm N}_{f,d,d}\big\vert_D\geq1
\quad\Longrightarrow\quad
\forall x,y\in D,\ d(f(x),f(y))=0?
$$

若不成立，从 (i) 中选取一个反例，并解释其正零化半径的来源。

</div>



<div data-mb-exercise="oet-aba6bee391edd367">

**习题 3.5（像集重排与覆盖估计）**：取 $\mathcal X=\mathbb R\sqcup\{\bot\}$，实数部分采用通常距离，按吸收元隔离公理扩展。令 $U=\{0,1,2,3\}$，定义算子 $f,g$ 在 $U$ 上的取值为

$$
\begin{array}{c|cccc}
x&0&1&2&3\\ \hline
f(x)&0&1&2&3\\
g(x)&0&3&1&2
\end{array}
$$

并令两个算子在 $\mathcal X\setminus U$ 上均取值 $\bot$。本题省略单分量下标。

**(i)** 求所有有限正数 $\varepsilon$ 下的 $\mathcal N(\varepsilon,U)$。特别地，解释在 $\varepsilon=7/4$ 时，为什么不能以 $3/2$ 为中心得到一个合法的内覆盖。

**(ii)** 求 $f(U)$、$g(U)$，比较两个像集在任意有限正精度下的覆盖数，并计算相应映射熵差。

**(iii)** 分别求 $f$、$g$ 在 $U$ 上最小的标量 Lip 常数。在精度 $\varepsilon=7/4$ 下，应用 [命题 3.19](<#user-content-oet-5f1e227b06f3a2d1>) 证明中的覆盖数上界，并将所得界与真实覆盖数比较。

</div>
