
<a id="oet-9e61c41837a10211"></a>

## 附录 D 习题解答

本附录按习题所在章节的顺序给出解答。各题的假设与记号以相应题面及其所在小节为准。

### 基础


<div data-mb-solution="oet-3250486e06e1af22" data-mb-for="oet-6f3c195f30ebebd6">

**习题 1.1 的解答**：

**(i)** 每个 $d_i$ 的自距零、对称性和三角不等式均由实数距离经 $q_i$ 拉回得到。添入 $\bot$ 后，自距零和对称性仍成立；含 $\bot$ 的三角不等式中，若两端只有一个是 $\bot$，则右侧至少一项为 $+\infty$，若中间点是 $\bot$ 而两端均不是，则右侧为 $+\infty$，其余情形直接成立。因此题给结构满足扩展规范空间的定义。

在 $U$ 内，半径为 $1$ 的 $d_1$-开球为 $\{a,c\}$、$\{b\}$，$d_2$-开球为 $\{a,b\}$、$\{c\}$。每种情形均需要且只需要两个中心，故

$$
\mathcal N_1(1,U)=\mathcal N_2(1,U)=2.
$$

任意两个不同点至少在一个分量下距离为 $1$，所以 $d_{\{1,2\}}=\max(d_1,d_2)$ 的半径 $1$ 开球都是单点集。因此

$$
\mathcal N_{\{1,2\}}(1,U)=3.
$$

**(ii)** 联合读数集合为

$$
\{(0,0),(1,0),(0,1)\}.
$$

虽然每个 $q_i$ 的值域都是 $\{0,1\}$，组合 $(1,1)$ 却没有对应的点。联合读数集合只是两个值域的笛卡尔积的真子集，两个读数不能任意组合；相应联合覆盖数也不等于两个单分量覆盖数之积。$\square$

分量伪度量分别规定如何比较点，并不预设这些区分结果能够独立组合。

</div>



<div data-mb-solution="oet-fae22ddbcb1da764" data-mb-for="oet-5e432018e992f2d3">

**习题 1.2 的解答**：

**(i)** 不同点间距离为 $\delta$ 或 $1$，均为正。自距零和对称性成立。对三个不同点，若都属于 $\{b_1,\ldots,b_m\}$，三角不等式化为 $\delta\le2\delta$；若包含 $a$，则只需检验 $1\le1+\delta$ 和 $\delta\le2$，均成立。因此 $d$ 在 $U$ 上是度量；添入隔离的吸收元得到扩展规范空间。

当 $0<\varepsilon\le\delta$ 时，每个开球与 $U$ 的交集都是单点集；当 $\delta<\varepsilon\le1$ 时，这些交集为 $\{a\}$ 与 $\{b_1,\ldots,b_m\}$；当 $\varepsilon>1$ 时，一个以 $U$ 内任意点为中心的开球即可覆盖 $U$。因此

$$
\mathcal N(\varepsilon,U)=
\begin{cases}
m+1,&0<\varepsilon\le\delta,\\
2,&\delta<\varepsilon\le1,\\
1,&\varepsilon>1,
\end{cases}
\qquad
E_\varepsilon(U)=
\begin{cases}
\log_2(m+1),&0<\varepsilon\le\delta,\\
1,&\delta<\varepsilon\le1,\\
0,&\varepsilon>1.
\end{cases}
$$

端点归属来自开球条件 $d(x,y)<\varepsilon$。

**(ii)** 对任意 $0<\eta\le1-\delta$，

$$
E_\delta(U)-E_{\delta+\eta}(U)=\log_2(m+1)-1.
$$

给定任意 $M>0$，取整数 $m\ge2$ 且 $m+1>2^{M+1}$，上式即大于 $M$。因此该增量没有与 $m$ 无关的上界，即使精度改变量 $\eta$ 任意小也是如此。$\square$

精度略大于 $\delta$ 时，一整个点簇可以由一个中心覆盖；到精度 $\delta$ 时，簇内每个点都需要单独覆盖。低熵刻画的是指定精度下的覆盖复杂度，不能据此限制更细精度下的复杂度。

</div>



<div data-mb-solution="oet-9125a5b5bee94d56" data-mb-for="oet-92cd0a940e038231">

**习题 1.3 的解答**：

**(i)** 所有算子均保持 $\bot$，所以 $d(\phi(\bot),\psi(\bot))=0$。由于 $U$ 有限非空，在 $\mathcal X$ 上取上确界等于在 $U$ 上取最大值，故

$$
d_{\mathrm{op}}(\phi,\psi)=\sup_{x\in\mathcal X}d(\phi(x),\psi(x))=\max_{x\in U}d(\phi(x),\psi(x)).
$$

对于 $d_{\mathrm{op}}^{\mathrm{av}}$，自距零与对称性逐项成立。逐点应用三角不等式、求和并乘以 $1/n$，得到

$$
d_{\mathrm{op}}^{\mathrm{av}}(\phi,\chi)
\le d_{\mathrm{op}}^{\mathrm{av}}(\phi,\psi)+d_{\mathrm{op}}^{\mathrm{av}}(\psi,\chi).
$$

若 $\phi\ne\bot_{\mathrm{op}}$，则存在 $x\in U$ 使 $\phi(x)\ne\bot$，相应求和项 $d(\phi(x),\bot)$ 为 $+\infty$。由于 $1/n>0$，有

$$
d_{\mathrm{op}}^{\mathrm{av}}(\phi,\bot_{\mathrm{op}})=+\infty.
$$

恒等算子提供非吸收算子，故所有公理均满足。

**(ii)** $\phi$ 与 $\psi$ 仅在 $x_1$ 处距离为 $1$，其余输入处距离为 $0$；$\phi$ 与 $\chi$ 在每个非吸收输入处距离均为 $1$。因此

$$
d_{\mathrm{op}}(\phi,\psi)=d_{\mathrm{op}}(\phi,\chi)=1,
$$

$$
d_{\mathrm{op}}^{\mathrm{av}}(\phi,\psi)=\frac1n,\qquad
d_{\mathrm{op}}^{\mathrm{av}}(\phi,\chi)=1.
$$

上确界记录最大的逐点距离，平均值还计入差异出现的输入点数量；在本题的离散度量下，对在 $U$ 上均有定义的两个算子，平均距离恰为输出不同的输入点所占比例。$\square$

</div>


### 算子界


<div data-mb-solution="oet-580f97e634e7ea13" data-mb-for="oet-b2cea3f1af318f29">

**习题 2.1 的解答**：

**(i)** 对任意 $x,y\in\mathbb R^2$，记 $a=|x_1-y_1|$、$b=|x_2-y_2|$。由三角不等式，

$$
d_1(\phi(x),\phi(y))=a=d_1(x,y),
$$

$$
\begin{aligned}
d_2(\phi(x),\phi(y))
&=a+|(x_1-y_1)+(x_2-y_2)|\\
&\le 2a+b\le 2(a+b)=2d_2(x,y).
\end{aligned}
$$

故题给的对角矩阵是 Lip 证书。

**(ii)** 此时

$$
\widetilde d_2(\phi(x),\phi(y))
=|(x_1-y_1)+(x_2-y_2)|
\le d_1(x,y)+\widetilde d_2(x,y),
$$

而第一分量仍满足等式，故可取

$$
\mathbf M=\begin{pmatrix}1&0\\1&1\end{pmatrix}.
$$

对任意 Lip 证书 $\mathbf M$，取 $x=(1,0)$、$y=(0,0)$，第二分量的 Lip 不等式给出

$$
1=\widetilde d_2(\phi(x),\phi(y))
\le M_{1\to2}\cdot1+M_{2\to2}\cdot0=M_{1\to2}.
$$

因此 $M_{1\to2}\ge1$。$\square$

两问保持映射 $\phi(s,t)=(s,s+t)$ 不变，改变的是规范结构。第一组规范的 $d_2$ 已经记录第一坐标的差异，因此允许 $L_{1\to2}=0$；改用只记录第二坐标差异的 $\widetilde d_2$ 后，任何 Lip 证书都必须满足 $M_{1\to2}\ge1$。映射的坐标依赖没有改变，但规范读取的差异改变了，上界中所需的分量项也随之改变。因此，解释 Lip 证书的零项时，必须结合所选的规范结构。

</div>



<div data-mb-solution="oet-76f9477eb8a341b9" data-mb-for="oet-6a98a58b5bc95360">

**习题 2.2 的解答**：

由 Lip 矩阵定义与 $L_{k\to j}=0$（$k\neq j$）：

$$
d_j(\phi(x), \phi(y)) \leq L_{j \to j} \cdot d_j(x, y).
$$

由 co-Lip 矩阵定义及各项非负，

$$
K_{j\to j}d_j(x,y)\le\sum_{k\in I}K_{k\to j}d_k(x,y)\le d_j(\phi(x),\phi(y)).
$$

合并即得。$\square$

若上述对角输入项条件对所有 $j \in I$ 均成立，则得到逐分量的标量双侧不等式。若进一步要求 $L_{j \to j}, K_{j \to j} < +\infty$，则得到有限标量双侧放缩界。

</div>


### 算子局部退化


<div data-mb-solution="oet-dbe28f0466504943" data-mb-for="oet-5a431d16f9d7ba6a">

**习题 3.1 的解答**：

**(i)** 由

$$
\phi(0)=-1,\qquad \phi(1)=1,
$$

得到 $\phi(U)=\{-1,1\}$。这两个输出虽不相等，却满足

$$
d_i(-1,1)=\bigl||-1|-|1|\bigr|=0.
$$

结合自距为零，得到

$$
\operatorname{Fib}_{\phi,i}(\phi(0)\mid U)=U,
$$

且 $i\in I_{\mathrm{const}}(\phi\mid U)$。

再次作用后，$\phi^2(x)=4x-3$，从而

$$
\phi^2(0)=-3,\qquad \phi^2(1)=1,\qquad d_i(-3,1)=2>0.
$$

因此

$$
\operatorname{Fib}_{\phi^2,i}(\phi^2(0)\mid U)=\{0\},
$$

且 $i$ 不属于 $\phi^2\mid U$ 的常值分量。又有

$$
d_i(\phi^2(0),0)=d_i(-3,0)=3>0,
$$

故 $i$ 也不属于恒等分量。因此 $i\in I_{\mathrm{act}}(\phi^2\mid U)$。

**(ii)** 不能。设替换后的算子为 $\widetilde\phi$，且存在 $c\in\mathbb R$，使得对所有 $x\in U$ 均有 $\widetilde\phi(x)=c$。则

$$
\widetilde\phi^2(x)=\widetilde\phi(c)\qquad(x\in U).
$$

若 $\widetilde\phi(c)\ne\bot$，则自复合输出仍是同一个点，$0,1$ 仍落入同一计算纤维，$i$ 仍属于常值分量。若 $\widetilde\phi(c)=\bot$，则 $U\cap\operatorname{dom}(\widetilde\phi^2)=\varnothing$，此时不能在 $U$ 上按本章定义讨论计算纤维，也不构成纤维分离。$\square$

第一问中的中间输出 $-1$ 与 $1$ 是不同的点，只是在所选伪度量下距离为零；再次作用的 $\phi$ 没有保持这对点的零距关系。落入同一计算纤维只表示当前输出在所选规范下零距，并不等同于输出点相同。

</div>



<div data-mb-solution="oet-c5c9191ff3f4d184" data-mb-for="oet-092ba6f495b988c1">

**习题 3.2 的解答**：

**(i)** 反设存在 $x\in U$，使得

$$
0<d_i(x,y)<r^{\mathrm N}_{\phi,i,j}(y\mid U).
$$

由零化半径的上确界定义，存在有限正半径 $\rho>d_i(x,y)$，使得

$$
B_i(y,\rho)\cap U\subseteq\operatorname{Fib}_{\phi,j}(\phi(y)\mid U).
$$

于是 $x\in B_i(y,\rho)\cap U$，故 $d_j(\phi(x),\phi(y))=0$。另一方面，由 co-Lip 下界（[§ 2.1](<02-operator-bounds.md#user-content-oet-af85899693cc8750>)）及各项非负，

$$
0=d_j(\phi(x),\phi(y))
\geq\sum_{k\in I}K_{k\to j}d_k(x,y)
\geq K_{i\to j}d_i(x,y)
>0,
$$

矛盾。因此 $d_i(x,y)$ 或为 $0$，或不小于 $r^{\mathrm N}_{\phi,i,j}(y\mid U)$。

**(ii)** 任取 $x,y\in U$。由下确界定义，

$$
0<\underline{r}^{\mathrm N}_{\phi,i,j}\big|_U\leq r^{\mathrm N}_{\phi,i,j}(y\mid U).
$$

若 $d_i(x,y)\ne0$，则由 (i) 得到

$$
d_i(x,y)\geq r^{\mathrm N}_{\phi,i,j}(y\mid U)\geq\underline{r}^{\mathrm N}_{\phi,i,j}\big|_U.
$$

这就给出所述统一距离间隙。$\square$

</div>



<div data-mb-solution="oet-26f07c9226b0ce42" data-mb-for="oet-fc424fbae1afcbdc">

**习题 3.3 的解答**：

**(i)** $d_i$ 的零距关系由绝对值相等确定。恒等算子在 $U$ 上的计算纤维分划为

$$
\bigl\{\{-3\},\{-2,2\},\{0\}\bigr\}.
$$

由

$$
\phi(-3)=-2,\qquad \phi(-2)=-1,\qquad \phi(0)=1,\qquad \phi(2)=3,
$$

得到 $\phi$ 在 $U$ 上的计算纤维分划为

$$
\bigl\{\{-3\},\{-2,0\},\{2\}\bigr\}.
$$

两种分划均有三个类，但

$$
d_i(-2,0)=2,\qquad d_i(\phi(-2),\phi(0))=0,
$$

$$
d_i(-2,2)=0,\qquad d_i(\phi(-2),\phi(2))=2.
$$

因此，原本分开的 $-2,0$ 被归入同一纤维，原本零距的 $-2,2$ 则落入不同纤维，两种分划互不细化。

**(ii)** 在输入端，$0$ 到 $U$ 中其余点的距离至少为 $2$，故任何半径 $\tfrac32$ 的内覆盖都必须以 $0$ 为一个中心，且至少还需一个中心。取中心 $0,-2$ 即可覆盖 $U$，所以

$$
\mathcal N_i(\tfrac32,U)=2.
$$

输出端为 $\phi(U)=\{-2,-1,1,3\}$。这些点到中心 $-2$ 的距离分别为 $0,1,1,1$，故

$$
\mathcal N_i(\tfrac32,\phi(U))=1.
$$

于是

$$
\Delta E_{\frac32,i}(\phi\mid U)=\log_2 2-\log_2 1=1.
$$

输入与输出的覆盖熵分别为 $1$ 和 $0$。与此同时，一对点由零距变成正距，另一对点由正距变成零距；输出覆盖熵为零也没有使三个计算纤维合为一个。$\square$

本题中的平移没有保持所选伪度量。映射熵差比较的是指定规范与精度下的覆盖数，其符号不能单独判定计算纤维分划的粗细，也不能概括所有点对距离的变化。

</div>



<div data-mb-solution="oet-bb4f6d46253f5edb" data-mb-for="oet-7ade05e895653cab">

**习题 3.4 的解答**：

**(i)** 计算结果如下：

| 局部输入域 $D$ | $\operatorname{diam}_d(D)$ | $\underline{r}^{\mathrm N}_{f,d,d}\big\vert_D$ | 阈值组合 |
| --- | --- | --- | --- |
| $[0,\tfrac12]$ | $\tfrac12$ | $+\infty$ | $(1,1)$ |
| $[\tfrac9{10},\tfrac{11}{10}]$ | $\tfrac15$ | $0$ | $(1,0)$ |
| $\{0,2\}$ | $2$ | $2$ | $(0,1)$ |
| $[0,2]$ | $2$ | $0$ | $(0,0)$ |

三个闭区间的直径均为两端点之差，二点集 $\{0,2\}$ 的直径为 $2$。

第一行中 $f$ 恒取 $0$，故全部有限正半径都有效。第二、四行都包含 $1$ 及任意接近 $1$ 的左侧点；对任意有限正数 $r$，取 $0<\delta<\min\{r,1/10\}$，则 $1-\delta$ 与 $1$ 的输入距离小于 $r$，输出分别为 $0$ 与 $1$。所以基点 $1$ 处没有有效的正零化半径，统一零化半径为 $0$。第三行中，半径不超过 $2$ 的开球只含相应基点，而半径大于 $2$ 的开球包含输出不同的另一点，故统一零化半径恰为 $2$。

**(ii)** 不成立。取 $D=\{0,2\}$，由 (i) 有

$$
\underline{r}^{\mathrm N}_{f,d,d}\big\vert_D=2\geq1,
\qquad
d(f(0),f(2))=2>0.
$$

这里的正零化半径来自输入域中的距离间隙：半径不超过 $2$ 的开球在 $D$ 中只含相应基点，并不要求两个不同输入的输出零距。同一算子在四个输入域上得到不同的阈值组合，说明这些读出必须连同所用输入域一起考察。$\square$

</div>



<div data-mb-solution="oet-e7bd21288ddb2bde" data-mb-for="oet-aba6bee391edd367">

**习题 3.5 的解答**：

**(i)** 不同点的距离至少为 $1$，所以 $0<\varepsilon\le1$ 时每个开球只能覆盖一个点，需要四个中心。

当 $1<\varepsilon\le2$ 时，中心集 $\{0,2\}$ 可以覆盖 $U$。另一方面，任何内部中心到某个端点的距离至少为 $2$，一个半径不超过 $2$ 的开球不能覆盖整个 $U$，因此至少需要两个中心。

当 $\varepsilon>2$ 时，以 $1$ 为中心即可覆盖 $U$。故

$$
\mathcal N(\varepsilon,U)=
\begin{cases}
4,&0<\varepsilon\le1,\\
2,&1<\varepsilon\le2,\\
1,&\varepsilon>2.
\end{cases}
$$

两个临界点的归属来自开球的严格不等式。虽然半径 $7/4$、中心 $3/2$ 的开球包含 $U$，但 $3/2\notin U$，不满足内覆盖的中心条件。

**(ii)** 两个像集均为 $U$。因此对任意有限正精度，

$$
\mathcal N(\varepsilon,f(U))=\mathcal N(\varepsilon,g(U))=\mathcal N(\varepsilon,U),
\qquad
\Delta E_\varepsilon(f\mid U)=\Delta E_\varepsilon(g\mid U)=0.
$$

**(iii)** $f$ 保持距离，故最小 Lip 常数为 $1$。对 $g$，不同输入的距离至少为 $1$，输出距离至多为 $3$，所以 $3$ 是合法 Lip 常数；输入对 $0,1$ 给出距离比 $3$，故最小常数恰为 $3$。

在 $\varepsilon=7/4$ 时，Lip 覆盖传递分别给出

$$
\mathcal N(7/4,f(U))\le\mathcal N(7/4,U)=2,
\qquad
\mathcal N(7/4,g(U))\le\mathcal N(7/12,U)=4.
$$

真实的两个像集覆盖数都为 $2$。前一个估计达到真实值，后一个估计并不紧。两个算子的像集及全部尺度的覆盖数完全一致，但输入与输出的对应不同，最小 Lip 常数也不同。因此，像集覆盖数描述输出集合在指定精度下需要多少中心，并不记录输出随输入顺序的往复变化。$\square$

</div>


### 算子链演算


<div data-mb-solution="oet-9bee8ae73f2048ff" data-mb-for="oet-51ab39dbe6ea409d">

**习题 4.1 的解答**：

**(i)** 两个输出分量的距离均为

$$
|(x_1-y_1)+(x_2-y_2)|\le d_1(x,y)+d_2(x,y),
$$

故

$$
\mathbf L=\begin{pmatrix}1&1\\1&1\end{pmatrix}
$$

是合法 Lip 矩阵。分别取 $x=(1,0),y=(0,0)$ 与 $x=(0,1),y=(0,0)$，可知任意合法 Lip 矩阵的每个条目都至少为 $1$。因此 $\mathbf L$ 是逐条目最小的证书。

$\mathbf L$ 的特征多项式为 $\lambda(\lambda-2)$，且 $\mathbf L^2=2\mathbf L$，所以

$$
\rho(\mathbf L)=2,\qquad \mathbf L^n=2^{n-1}\mathbf L\quad(n\ge1).
$$

另一方面，

$$
\phi^2(s,t)=\phi(s+t,-s-t)=(0,0),
$$

故 $\phi^n(s,t)=(0,0)$ 对所有 $n\ge2$ 成立；吸收元始终映为自身。

固定证书的矩阵幂逐条目增长，实际算子却在两步后将实数部分映为同一点。原因在于第一步的像落在直线 $t=-s$ 上，第二步在该像域上恒为零。因此，若逐步限制到真实像域，第二步即可选取零矩阵作为 Lip 证书；反复使用全域的 $\mathbf L$ 没有利用这一信息。

**(ii)** 当 $x\ne y$ 时，

$$
\frac{|\psi(x)-\psi(y)|}{|x-y|}=1+x^2+xy+y^2\ge1.
$$

因而单分量矩阵 $\mathbf K=(1)$ 合法。取 $x=t\ne0,y=0$，该比值为 $1+t^2$，随 $t\to0$ 趋于 $1$，所以任何合法单分量 co-Lip 证书都不超过 $1$。故最大证书为 $\mathbf K=(1)$，且 $\rho(\mathbf K)=1$。

固定 $x\ne y$，记

$$
x_n=\psi^n(x),\qquad y_n=\psi^n(y),\qquad \delta_n=|x_n-y_n|.
$$

由

$$
x_n^2+x_ny_n+y_n^2
=\frac14(x_n-y_n)^2+\frac34(x_n+y_n)^2
\ge\frac14\delta_n^2,
$$

得到

$$
\delta_{n+1}\ge\left(1+\frac{\delta_n^2}{4}\right)\delta_n\ge\delta_n.
$$

于是 $\delta_n\ge\delta_0>0$，进一步归纳得

$$
\delta_n\ge\delta_0\left(1+\frac{\delta_0^2}{4}\right)^n\longrightarrow+\infty.
$$

因此，每对不同点的迭代距离都趋于无穷，尽管全域上不存在谱半径大于 $1$ 的单分量 co-Lip 证书。这里，每个固定点对都有自己的大于 $1$ 的增长率，但这些增长率在初始距离趋于零时可以任意接近 $1$。$\square$

两问分别使用了最小的 Lip 证书和最大的 co-Lip 证书，差距并非来自任意放松证书。谱条件给出充分保证（参见 [命题 4.5](<04-operator-chain-calculus.md#user-content-oet-cb1aac0882bde4ae>)）；这些条件不满足时，仍需考察实际像域、具体点对或多步作用，不能据此反推相反的迭代行为。

</div>



<div data-mb-solution="oet-92845f1b79fdc073" data-mb-for="oet-0ff7986894ec9221">

**习题 4.2 的解答**：

记 $c_0=\operatorname{id}_{\mathcal X}$，$c_m=\phi_m\circ\cdots\circ\phi_1$。当 $m=1$ 时，$c_0=\operatorname{id}_{\mathcal X}$ 且 $\overleftarrow{\prod}_{r=1}^{0}\mathbf L^{(r)}=\mathbf I$，故下式成为等式。每进一步，把已得分量上界代入下一步的 Lip 不等式；矩阵条目非负，故保持不等号方向。对步数归纳，得到对任意 $m\ge1$，

$$
d_{i^*}(c_{m-1}(x),c_{m-1}(x'))
\le
\sum_{i\in I}\left[\overleftarrow{\prod}_{r=1}^{m-1}\mathbf L^{(r)}\right]_{i\to i^*}d_i(x,x').
$$

右侧趋于 $0$，故存在 $M\ge m_0$，使得对所有 $m\ge M$，

$$
d_{i^*}(c_{m-1}(x),c_{m-1}(x'))<r^{\mathrm N}_0.
$$

此时 $c_{m-1}(x),c_{m-1}(x')\in U_m$，且

$$
d_{i^*}(c_{m-1}(x),c_{m-1}(x'))
<
r^{\mathrm N}_0
\le
r^{\mathrm N}_{\phi_m,i^*,j^*}(c_{m-1}(x)\mid U_m).
$$

由零化半径定义（[§ 3.3](<03-operator-local-degeneracy.md#user-content-oet-bb1487a09d8bf151>)），第 $m$ 步在输出分量 $j^*$ 上将该点对归零，即 $d_{j^*}(c_m(x),c_m(x'))=0$。$\square$

把 $x$ 与 $x'$ 看作初始状态及其扰动状态，本题说明：在所给条件下，初始扰动沿链传播后，从某一步起在指定输出伪度量下变得不可分辨。

</div>



<div data-mb-solution="oet-f52ddbdb4056399a" data-mb-for="oet-b7e77b504317782a">

**习题 4.3 的解答**：

**(i)** 初始熵有限。对 $1\le m\le r$，假设第 $m$ 个熵有限，记其值为 $e_m$。若后继熵为 $+\infty$，则

$$
\Delta E_{\varepsilon,i}(\phi_m\mid U_m)
=e_m-(+\infty)=-\infty,
$$

与熵差下界 $\delta>0$ 矛盾。因此后继熵也有限；又因 $U_{m+1}$ 非空，其熵非负。记其值为 $e_{m+1}$，便可在实数中计算

$$
e_m-e_{m+1}=\Delta E_{\varepsilon,i}(\phi_m\mid U_m)\ge\delta,
\qquad e_{m+1}\le e_m-\delta.
$$

归纳即得 $U_1,\ldots,U_{r+1}$ 上的熵均为有限非负实数，并满足所述递推不等式。

**(ii)** 若 $k^*=0$，由 $e_1/\delta\ge0$ 及 $\lceil e_1/\delta\rceil=0$ 得 $e_1=0$，取 $m=1$ 即可。以下设 $k^*\ge1$。

若 $U_1,\ldots,U_{k^*}$ 中已有一个集合的熵为零，结论成立。否则这些熵均为正，由 (i)（取 $r=k^*\le k$）可将前缀熵写成有限非负实数 $e_1,\ldots,e_{k^*+1}$。逐步应用递推不等式，得到

$$
0\le e_{k^*+1}\le e_1-k^*\delta\le0,
$$

其中最后一步由 $k^*=\lceil e_1/\delta\rceil$ 得出。因此 $E_{\varepsilon,i}(U_{k^*+1})=0$，取 $m=k^*+1$ 即得结论。$\square$

</div>


### 算子网络


<div data-mb-solution="oet-ec0a45eb2c508cb8" data-mb-for="oet-96bb1a4734f21c32">

**习题 5.1 的解答**：

局域算子的定义域与像均为 $\mathbb N_0$，故自环转移域 $\mathbb N_{>0}$ 满足源像与目标域条件，终止域为 $\{0\}$。对输入 $n\ge1$，唯一终止轨迹为

$$
(\beta,n)\leadsto(\beta,n-1)\leadsto\cdots\leadsto(\beta,1),
$$

其终止输出为 $f_\beta(1)=0$，长度恰为 $n$。这里正常点 $0$ 与吸收元 $\bot$ 不同。

**(i)** 入口与各步后继唯一，每个输入都在有限步后终止，且唯一节点被经过。但对任意候选统一长度界 $N$，输入 $N+1$ 的轨迹长度为 $N+1$。因此不存在统一有限长度界，这些数据不构成本章的有限算子网络。

**(ii)** 当入口片为 $U_m$ 时，每个输入 $n$ 的轨迹长度为 $n\le m$；节点 $\beta$ 被输入 $1$ 的轨迹经过。因此，入口分划、出边互斥、统一有限终止与无冗余节点四条条件全部成立。外延算子为

$$
\phi_{\mathcal N_m}(x)
=
\begin{cases}
0,&x\in\{1,\ldots,m\},\\
\bot,&x\notin\{1,\ldots,m\}.
\end{cases}
$$

输入 $m$ 的轨迹长度为 $m$，故 $\operatorname{Depth}(\mathcal N_m)=m$。全部可达路径为由 $k$ 个 $\beta$ 组成的序列 $p_k=(\beta,\ldots,\beta)$，其中 $1\le k\le m$，且

$$
U_{p_k}=\{k\}.
$$

其他节点序列的路径域为空。$\square$

</div>



<div data-mb-solution="oet-2316b12692553c3b" data-mb-for="oet-171f4e850e8f1c36">

**习题 5.2 的解答**：

取 $\mathcal X=\{\bot,a,b,c\}$，四点互异，正常点间可取离散距离。取两个节点 $\alpha,\beta$，局域算子为

$$
f_\alpha=\mathrm{id}_{\mathcal X}|_{\{a,c\}},
\qquad
f_\beta=\mathrm{id}_{\mathcal X}|_{\{b,c\}}.
$$

入口片为 $U_\alpha^{\mathrm{in}}=\{a\}$、$U_\beta^{\mathrm{in}}=\{b\}$，两条边及其转移域为

$$
\alpha\to\beta,\quad D_{\alpha\to\beta}=\{c\},
\qquad
\beta\to\alpha,\quad D_{\beta\to\alpha}=\{c\}.
$$

两条边域均非空，且均包含于相应的源像与目标定义域；每个节点只有一条出边。原终止域分别为 $T_\alpha=\{a\}$、$T_\beta=\{b\}$。

输入 $a,b$ 分别在节点 $\alpha,\beta$ 一步终止，输出分别为 $a,b$。因此网络深度为 $1$，两个节点均被经过，全部网络条件成立；但两条边都不被任何入口求值轨迹经过。原图具有闭路 $\alpha\to\beta\to\alpha$。

节点实际输入域为

$$
U_\alpha^{\mathrm{eff}}=\{a\},
\qquad U_\beta^{\mathrm{eff}}=\{b\}.
$$

有效约化保留两个节点及其入口片，将局域算子分别限制为 $\mathrm{id}_{\mathcal X}|_{\{a\}}$、$\mathrm{id}_{\mathcal X}|_{\{b\}}$。两条有效边域均为空，故不再记录边；有效终止域仍分别为 $\{a\}$、$\{b\}$。所得无边图无环。$\square$

</div>



<div data-mb-solution="oet-306970c6d8944d2e" data-mb-for="oet-ff997c4726870929">

**习题 5.3 的解答**：

**(i)** 两条入口片非空且互不相交。节点 $\alpha$ 将 $\{-2,-1\}$ 映为 $\{1,2\}$，节点 $\beta$ 保持 $\{1,2\}$ 不变，因此两条边均满足转移域条件。节点 $\gamma$ 无出边，两类输入均在经过两个节点后终止；三个节点都被实际经过。故这些数据构成有限算子网络，求值深度为 $2$。

全部可达路径及其路径域为

$$
p_-=(\alpha,\gamma),\quad U_{p_-}=\{-2,-1\},
\qquad
p_+=(\beta,\gamma),\quad U_{p_+}=\{1,2\}.
$$

两个路径链在正常点上都为 $x\mapsto x^2$，故

$$
\phi_{\mathcal N}(x)
=
\begin{cases}
x^2,&x\in\{-2,-1,1,2\},\\
\bot,&x\notin\{-2,-1,1,2\}.
\end{cases}
$$

**(ii)** 这里 $q=p_-$、$q'=p_+$ 本身就是完整路径，因而

$$
U[q\ast]=\{-2,-1\},\qquad U[q'\ast]=\{1,2\},
$$

但

$$
D_q^{\mathrm{in}}=D_{q'}^{\mathrm{in}}=\{1,2\},
\qquad
D_q^{\mathrm{out}}=D_{q'}^{\mathrm{out}}=\{1,4\}.
$$

三个节点的实际输入域为

$$
U_\alpha^{\mathrm{eff}}=\{-2,-1\},
\qquad U_\beta^{\mathrm{eff}}=U_\gamma^{\mathrm{eff}}=\{1,2\}.
$$

所以，初始输入片互不相交并不保证当前输入域互不相交：不同分支的前置作用可以把不同初始输入送到同一组当前点值。

**(iii)** 复制后仅有路径 $(\alpha,\gamma_-)$、$(\beta,\gamma_+)$，路径域仍分别为 $\{-2,-1\}$、$\{1,2\}$。两条路径都长为 $2$，各步作用与原路径相同；四个节点均被经过，故复制后仍为有限算子网络。

令 $s$ 为正常点上 $s(x)=x^2$、在 $\bot$ 处取 $\bot$ 的算子。两网的路径分段读出均为

$$
\{\{-2,-1\}:s,\ \{1,2\}:s\},
$$

外延算子也相同。原网络的两条路径共享末节点 $\gamma$，复制后的两条路径使用不同末节点。标记表达的同构要求同一全局节点重命名保持标签共享关系；原网络有三个节点，复制后有四个节点，不存在这样的节点双射。因此两网不有效等价。$\square$

</div>



<div data-mb-solution="oet-3cc7030ed4bca738" data-mb-for="oet-b3e92d181e7139bd">

**习题 5.4 的解答**：

两个节点的定义域均为 $\mathbb R$，像分别为 $\{0\}$、$\{1\}$。两个非空入口片分划

$$
U=(-1,0)\cup(0,1).
$$

由于没有边，每个输入在其入口节点一步终止，两个节点都被经过，故网络条件成立。仅有两条单节点路径，路径域分别为 $(-1,0)$、$(0,1)$，外延算子为

$$
\phi_{\mathcal N}(x)
=
\begin{cases}
0,&-1<x<0,\\
1,&0<x<1,\\
\bot,&x\notin U.
\end{cases}
$$

每条路径链在其路径域上为常值，故输出距离恒为零，可取 Lip 上界 $0$，也可取任意有限正上界。

若整个 $U$ 上存在有限 Lip 上界 $L\ge0$，则对每个整数 $n\ge2$，取 $x_n=-1/n$、$y_n=1/n$，有

$$
1=|\phi_{\mathcal N}(x_n)-\phi_{\mathcal N}(y_n)|
\le L|x_n-y_n|=\frac{2L}{n}.
$$

选择整数 $n>\max\{2,2L\}$ 即得矛盾。因此，路径内的有限 Lip 上界不足以控制跨路径点对。$\square$

</div>



<div data-mb-solution="oet-487efe0b30cd3fb1" data-mb-for="oet-082bb5a4fb2472b9">

**习题 5.5 的解答**：

记 $\mathcal M=\mathcal N^{\mathrm{eff}}$。有效约化保持每个初始输入的完整节点序列与各步当前点值，所以，按相同标签比较，有

$$
U_\beta^{\mathrm{eff},\mathcal M}
=U_\beta^{\mathrm{eff},\mathcal N}
\qquad(\beta\in V).
$$

记右侧为 $A_\beta$。$\mathcal M$ 的局域算子为 $f_\beta|_{A_\beta}$，其定义域正是 $A_\beta$；再次限制到实际输入域 $A_\beta$ 不改变该算子。入口片在两次有效约化中均保持不变。

对 $\mathcal M$ 的任一边 $\beta\to\gamma$，记其边域为 $D^{\mathcal M}_{\beta\to\gamma}$。由第一次有效约化的定义，

$$
D^{\mathcal M}_{\beta\to\gamma}
=f_\beta(A_\beta)\cap D^{\mathcal N}_{\beta\to\gamma}
\subseteq f_\beta(A_\beta).
$$

而 $\mathcal M$ 在节点 $\beta$ 的实际输出像仍为 $f_\beta(A_\beta)$，故第二次有效约化的边域为

$$
f_\beta(A_\beta)\cap D^{\mathcal M}_{\beta\to\gamma}
=D^{\mathcal M}_{\beta\to\gamma}.
$$

第一次约化中删除的空边不会重新出现，保留边的边域也不再改变。同理，由

$$
T_\beta^{\mathcal M}=f_\beta(A_\beta)\cap T_\beta^{\mathcal N}
\subseteq f_\beta(A_\beta)
$$

可知终止域在第二次约化中保持不变。节点集、局域算子、入口片、边集与边域全部相同，所以 $\mathcal M^{\mathrm{eff}}=\mathcal M$。$\square$

</div>



<div data-mb-solution="oet-f301458f635b5a6f" data-mb-for="oet-8570ea1bf1a8708b">

**习题 5.6 的解答**：

**(i)** 由 [命题 5.16](<05-operator-networks.md#user-content-oet-2498621c42325300>) 的证明，每步都有

$$
M(\mathcal N_{j+1})+1\le M(\mathcal N_j).
$$

相加得到 $M(\mathcal N_k)+k\le M(\mathcal N_0)$。因 $M(\mathcal N_k)\ge0$，即得步数界。

**(ii)** 记 $\mathcal N_m$ 为经历 $m$ 次加细后的网络。它由 $m+1$ 个 $e$ 节点串联，唯一入口片为 $\{a\}$；每个非末节点的唯一出边域为 $\{a\}$，末节点没有出边。输入 $a$ 逐个经过全部节点，点值始终为 $a$，故轨迹长度恒为 $m+1$，全部节点均实际发生，且

$$
|V_{\mathcal N_m}|=\operatorname{Depth}(\mathcal N_m)=m+1,
\qquad
\phi_{\mathcal N_m}=e.
$$

由于 $e(\{a\})=\{a\}$ 且 $e\circ e=e$，将任一节点替换为两个 $e$ 节点满足代数加细的定义，并使串联长度增加 $1$。同样的分解可以反复使用，所以得到无限合法加细序列。

**(iii)** (i) 只允许真节点域分划；(ii) 使用代数加细，单点域并未被分割。事实上后者各网络的 $M$ 都等于 $0$，不能作为严格下降量。若存在自然数值函数 $\mu$ 对其每步严格下降，则对任意 $m$ 有

$$
\mu(\mathcal N_m)+m\le\mu(\mathcal N_0),
$$

取 $m=\mu(\mathcal N_0)+1$ 即矛盾。对局域算子秩，允许 $e=e\circ e$ 将要求

$$
2r(e)<r(e),
$$

这对自然数 $r(e)$ 不可能成立。可见固定网络的有限求值并不提供表示加细的终止证书。$\square$

</div>


### 分离规范特化


<div data-mb-solution="oet-b513dd0ddd9bb63f" data-mb-for="oet-218697f5beb9e317">

**习题 A.1 的解答**：

**(i)** 设 $x,y\in U$ 且 $\phi(x)=\phi(y)$。对每个 $i\in I$，选取使 $K_{i\to j}>0$ 的 $j$。由 co-Lip 不等式，

$$
0\le K_{i\to j}d_i(x,y)
\le\sum_{a\in I}K_{a\to j}d_a(x,y)
\le d_j(\phi(x),\phi(y))=0.
$$

正的扩展非负系数与 $d_i(x,y)$ 的乘积为零，故 $d_i(x,y)=0$。这对全部 $i$ 成立，族分离性给出 $x=y$。正对角条件对应于每个 $i$ 都选取 $j=i$，所以是本题条件的特例。

**(ii)** 坐标交换满足

$$
d_1(\phi(x),\phi(y))=d_2(x,y),\qquad
d_2(\phi(x),\phi(y))=d_1(x,y).
$$

因此题设矩阵在各输出分量的 co-Lip 不等式中均取等号。每个输入分量均有一个系数为 $1$ 的输出通道，故 **(i)** 适用，而该矩阵的两个对角条目均为零。

进一步，设 $\mathbf K'$ 为任意合法 co-Lip 矩阵。将点对 $(1,0),(0,0)$ 代入第一输出分量的不等式，得到 $K'_{1\to1}\le0$；将点对 $(0,1),(0,0)$ 代入第二输出分量的不等式，得到 $K'_{2\to2}\le0$。各条目非负，故两个对角条目都为零。该算子单射，却不存在正对角 co-Lip 证书。

**(iii)** 若 $x,y\in[0,1]$ 且 $x^2=y^2$，则 $(x-y)(x+y)=0$。若 $x+y=0$，由非负性得 $x=y=0$；否则 $x-y=0$。所以 $\psi\big|_V$ 单射。

设 $K$ 为合法 co-Lip 常数。比较 $1$ 与 $0$，得到 $K\le1$，从而 $K$ 有限。若 $K>0$，取 $t=K/2\in(0,1]$。比较 $t$ 与 $0$，得到

$$
Kt\le t^2,
\qquad\text{从而}\qquad
K\le t=K/2,
$$

矛盾。因此 $K=0$；反之，$K=0$ 显然满足全部 co-Lip 不等式。单射性并不保证存在正的统一 co-Lip 下界，故 **(i)** 的正通道条件也不是必要条件。$\square$

</div>



<div data-mb-solution="oet-284115228e66da7c" data-mb-for="oet-93e134ff76be8bc0">

**习题 A.2 的解答**：

**(i)** 因 $f$ 为恒等映射、通常距离分离点，$1/n$ 的计算纤维是单点集 $\{1/n\}$。其最近的不同点为 $1/(n+1)$，距离为

$$
g_n=\frac1n-\frac1{n+1}=\frac1{n(n+1)}.
$$

确实，若 $m>n$，则 $1/n-1/m\ge g_n$；若 $m<n$，则 $n\ge2$，且

$$
\frac1m-\frac1n\ge\frac1{n-1}-\frac1n
=\frac1{n(n-1)}>g_n.
$$

因此半径不超过 $g_n$ 的开球在 $U$ 内只有基点，而半径大于 $g_n$ 时包含 $1/(n+1)$。故

$$
r^{\mathrm N}_{f,d,I}(1/n\mid U)=g_n>0,
\qquad
\underline{r}^{\mathrm N}_{f,d,I}\big|_U
=\inf_{n\ge1}g_n=0.
$$

最后一个等号可由 $0<g_n\le1/n$ 得到。

对任意有限正数 $r$，取正整数 $N$ 使 $1/N<r$，并令

$$
S_N=\{1/k:1\le k\le N\}\subseteq U.
$$

前 $N$ 个点均为球心；对 $n>N$，有 $|1/n-1/N|<1/N<r$。因此 $S_N$ 给出半径 $r$ 的有限内覆盖，$\mathcal N_I(r,U)\le N$。然而 $f(U)=U$ 是无限集。

**(ii)** 正整数中任意两不同点的距离至少为 $1$，且每个 $n$ 都有距离恰为 $1$ 的邻点 $n+1$。与 **(i)** 相同的开球论证给出

$$
r^{\mathrm N}_{f,d,I}(n\mid V)=1\quad(n\in V),
\qquad
\underline{r}^{\mathrm N}_{f,d,I}\big|_V=1.
$$

半径 $1$ 的开球在 $V$ 内都是单点，有限多个这样的球不能覆盖 $V$，所以 $\mathcal N_I(1,V)=+\infty$。恒等映射的像 $f(V)=V$ 仍无限。

第一例有任意正尺度的有限覆盖和逐点正半径，却没有统一正半径；第二例有统一正半径，却没有同一半径下的有限覆盖。两者分别说明题述有限像结论的两个条件不能按题中方式削弱或删去。$\square$

</div>



<div data-mb-solution="oet-7e21c861157c9002" data-mb-for="oet-38e12b6f9364127f">

**习题 A.3 的解答**：

**(i)** 先设统一零化半径为 $+\infty$。它是各基点零化半径的下确界，故每个 $y\in U$ 均有 $r^{\mathrm N}_{f,d_I,I}(y\mid U)=+\infty$。任取 $x,y\in U$ 且 $d_I(x,y)<+\infty$，由半径的上确界定义，存在合法的有限正半径 $r>d_I(x,y)$。于是 $x\in B_I(y,r)\cap U$，故

$$
d_i(f(x),f(y))=0\qquad(\forall i\in I).
$$

族分离性给出 $f(x)=f(y)$。

反之，设所有有限 $d_I$ 距离的点对都被映到同一点。任取 $y\in U$ 与有限正数 $r$。对每个 $x\in B_I(y,r)\cap U$，有 $d_I(x,y)<r<+\infty$，故 $f(x)=f(y)$。因此每个有限正半径都合法，$r^{\mathrm N}_{f,d_I,I}(y\mid U)=+\infty$；再对 $y\in U$ 取下确界即得统一半径为 $+\infty$。

若所有点对距离有限，上述等价便给出任意 $x,y\in U$ 都有 $f(x)=f(y)$。固定非空集 $U$ 中的一点即可得到 $f\big|_U$ 常值。证明只需逐对距离有限，不需要为全部点对距离选取共同的有限上界，因而无须直径有限。

**(ii)** 题设距离对称、自距为零，并满足三角不等式：若两端点不同，任意中间点至少与其中一端不同，所以右侧至少有一项为 $+\infty$。不同点距离为 $+\infty>0$，故族分离性与吸收元隔离均成立。

任意有限半径的球都只有球心，因此恒等算子在每个这样的球与 $U$ 的交上为常值。每个基点的零化半径以及统一零化半径均为 $+\infty$，但 $f(a)=a\ne b=f(b)$。这不违反 **(i)**：点对 $(a,b)$ 的距离为 $+\infty$，不在其中的有限距离条件内。$\square$

</div>


### 有限维实坐标模型

本节的实矩阵运算沿用 [§ B.2](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-a81f07d81e16c501>) 中的有限条目识别约定。


<div data-mb-solution="oet-a1e02f0ce54cbc38" data-mb-for="oet-1873ded007b293ec">

**习题 B.1 的解答**：

由欧氏范数的坐标表达，

$$
d_{\mathrm{Euc}}(x,y)^2
=\sum_{i=1}^n|x_i-y_i|^2
=\sum_{i\in\operatorname{supp}(x-y)}d_i(x,y)^2.
$$

和式包含 $|\operatorname{supp}(x-y)|$ 个非零项，每项不超过 $d_I(x,y)^2$，故取平方根得到第二式。$\square$

</div>



<div data-mb-solution="oet-398de9e7403804ea" data-mb-for="oet-f09514ceb9b32a5a">

**习题 B.2 的解答**：

**(i)** 非负矩阵的 $\ell^1$ 诱导范数等于最大列和，因此

$$
\|\mathbf L\|_{1\to1}
=\max_{i\in I}\sum_{j\in I}L_{i\to j}
\le cL_{\max}.
$$

对任意 $u\in\mathbb R^n$，逐行使用 Cauchy-Schwarz 不等式，得到

$$
\begin{aligned}
\|\mathbf L u\|_2^2
&=\sum_{j\in I}\left(\sum_{i\in I}L_{i\to j}u_i\right)^2\\
&\le\sum_{j\in I}\left(\sum_{i\in I}(L_{i\to j})^2\right)\|u\|_2^2\\
&\le mL_{\max}^2\|u\|_2^2.
\end{aligned}
$$

最后一步利用平方和至多有 $m$ 个非零项，每项不超过 $L_{\max}^2$。取平方根，再对单位向量取上确界，便得欧氏算子范数界；这一论证也包括 $m=0$ 的零矩阵情形。

**(ii)** 由 [命题 B.6](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5386499e20ce893d>)，

$$
d_{\mathrm{Euc}}(\phi(x),\phi(y))
\le\|\mathbf L\|_{2\to2}d_{\mathrm{Euc}}(x,y).
$$

代入 **(i)** 的欧氏算子范数界即可。$\square$

</div>



<div data-mb-solution="oet-f10025224540eb02" data-mb-for="oet-661612e2b84e7cff">

**习题 B.3 的解答**：

非零条目恰为 $(B_n)_{1\to j}$（$j\in I$），所以共有 $n$ 个，占 $n^2$ 个位置的比例为 $n/n^2=1/n$。每行的和均为 $1$，故 $\|\mathbf B_n\|_{\infty\to\infty}=1$。

对任意 $u\in\mathbb R^n$，有 $\mathbf B_nu=(u_1,\ldots,u_1)$，从而

$$
\|\mathbf B_nu\|_2=\sqrt n\,|u_1|\le\sqrt n\,\|u\|_2.
$$

取 $u=e_1$ 时 $\|u\|_2=1$ 且上式取等号，故 $\|\mathbf B_n\|_{2\to2}=\sqrt n$。当 $n\to\infty$ 时，非零比例趋于零，欧氏算子范数却趋于无穷。

这里每个输出分量只接收同一个输入分量，最大分量放大始终为 $1$；欧氏范数则累加了 $n$ 个输出分量的平方。[推论 B.7](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-36ae8406e21d3213>) 控制的是最大范数，因此与本例一致。$\square$

</div>



<div data-mb-solution="oet-5afd1eb9ec42078b" data-mb-for="oet-4f0e5a8aa7221640">

**习题 B.4 的解答**：

**(i)** 当 $x-y\in V_a$ 时，对 $c\ne a$ 有 $P_c(x-y)=0$，而 $P_a(x-y)=x-y$。将此代入 [命题 B.9](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-460dce986b592798>) 的不等式，得到

$$
\|P_b(F(x)-F(y))\|_2
\le
L^V_{a\to b}\|x-y\|_2.
$$

若 $L^V_{a\to b}=0$，则左端为零，故 $P_bF(x)=P_bF(y)$。

**(ii)** 若所有 $b\ne a$ 均满足 $L^V_{a\to b}=0$，则由 (i) 和正交直和分解，

$$
F(x)-F(y)
=\sum_{b\in H}P_b(F(x)-F(y))
=P_a(F(x)-F(y))\in V_a.
$$

这就得到第二部分。$\square$

</div>



<div data-mb-solution="oet-7d0cea475a47b225" data-mb-for="oet-ad5d1c84e576f84a">

**习题 B.5 的解答**：

按上述约定，将有限 Lip 矩阵不等式读作实数不等式，得到

$$
d_j(\phi(x),\phi(y))
\le
\sum_{i\in I}L_{i\to j}d_i(x,y).
$$

当 $i\notin \operatorname{supp}_j(\mathbf L)$ 或 $i\notin\operatorname{supp}(x-y)$ 时，对应项为零。其余每一项不超过 $L_{\max}d_I(x,y)$，故第一式成立。再对 $j$ 取最大值得第二式。$\square$

</div>



<div data-mb-solution="oet-437f5f735cb4fcf7" data-mb-for="oet-ac7cdc1d2ab36d93">

**习题 B.6 的解答**：

**(i)** 若 $F_j$ 在 $U$ 上为常值，则其梯度处处为零。反之，设 $\nabla F_j$ 在 $U$ 上处处为零，并固定 $x_0\in U$。对任意 $x\in U$，凸性保证线段 $x_0+t(x-x_0)$（$0\le t\le1$）包含于 $U$。由连续可微性与微积分基本定理，

$$
F_j(x)-F_j(x_0)
=
\int_0^1
\langle\nabla F_j(x_0+t(x-x_0)),x-x_0\rangle\,dt
=0.
$$

故 $F_j$ 在 $U$ 上恒等于 $F_j(x_0)$。在坐标规范下，输出的第 $j$ 分量零距等价于对应坐标相等；因此上述常值条件也恰好等价于 $j\in I_{\mathrm{const}}(\phi_F\mid U)$。

**(ii)** 令 $G_j(x)=F_j(x)-x_j$，则

$$
\nabla G_j(x)=\nabla F_j(x)-e_j.
$$

若 $F_j(x)=x_j$ 对所有 $x\in U$ 成立，则 $G_j$ 恒为零，因而 $\nabla F_j=e_j$，且 $F_j(x_0)=(x_0)_j$。反之，梯度条件与 (i) 的论证给出 $G_j$ 在 $U$ 上为常值；基点条件给出 $G_j(x_0)=0$，故 $G_j$ 处处为零，即 $F_j(x)=x_j$。

最后核对恒等分量定义中的常值排除条件。由于 $U$ 开且 $x_0\in U$，存在 $\delta>0$ 使 $x_0+\delta e_j\in U$。这两点的第 $j$ 坐标相差 $\delta$，所以坐标函数 $x\mapsto x_j$ 在 $U$ 上不是常值。于是 $F_j(x)=x_j$ 同时给出逐点的第 $j$ 分量零距和非常值性，恰好等价于 $j\in I_{\mathrm{id}}(\phi_F\mid U)$。$\square$

</div>



<div data-mb-solution="oet-a6e44fe8709f399e" data-mb-for="oet-291a10c8f6ac11cb">

**习题 B.7 的解答**：

由 $F(s,t)=F(y_1,y_2)$ 当且仅当 $s=y_1$，得到

$$
F^{-1}(F(y))=\{(y_1,t):t\in\mathbb R\}.
$$

线性部分 $T=\operatorname{diag}(1,0)\ne0$，由 [命题 B.14](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-055e3702cf9c3930>) 的 (ii)，

$$
r^{\mathrm N}_{\phi_F,d_I,I}(y\mid\mathbb R^2)=0.
$$

纤维允许第二个坐标任意变化，却要求第一个坐标固定。任意 $r>0$ 的全族输入球中都包含点 $x=(y_1+r/2,y_2)$，它满足 $\|x-y\|_\infty=r/2<r$，但 $F(x)\ne F(y)$。因此该直线不包含任何以 $y$ 为中心的全族输入小球。$\square$

</div>



<div data-mb-solution="oet-69a2b7cc4abd53c5" data-mb-for="oet-ef39fb9c4b025f07">

**习题 B.8 的解答**：

**(i)** 当 $k=1$ 时，待证式就是题设递推，余项前的空矩阵乘积为恒等矩阵。设结论已对前 $k-1$ 步成立。由于 $\mathbf M^{(k)}$ 逐条目非负，左乘该矩阵保持逐分量不等式，故

$$
\begin{aligned}
e^{(k)}
&\le \mathbf M^{(k)}e^{(k-1)}+r^{(k)}\\
&\le \mathbf M^{(k)}\cdots\mathbf M^{(1)}e^{(0)}
+\sum_{m=1}^{k-1}
\mathbf M^{(k)}\cdots\mathbf M^{(m+1)}r^{(m)}
+r^{(k)}\\
&= \mathbf M^{(k)}\cdots\mathbf M^{(1)}e^{(0)}
+\sum_{m=1}^{k}
\mathbf M^{(k)}\cdots\mathbf M^{(m+1)}r^{(m)}.
\end{aligned}
$$

最后一步把 $r^{(k)}$ 写成恒等矩阵作用于该向量。归纳即得结论；整个论证没有要求初始向量 $e^{(0)}$ 为零。

**(ii)** (i) 两侧均逐分量非负，故可对逐分量不等式取 $\ell^\infty$ 范数。再使用三角不等式、矩阵算子范数界及其次乘性，得到

$$
\|e^{(k)}\|_\infty
\le
\left(\prod_{t=1}^k\alpha_t\right)\|e^{(0)}\|_\infty
+\sum_{m=1}^k
\left(\prod_{t=m+1}^k\alpha_t\right)\|r^{(m)}\|_\infty.
$$

其中 $m=k$ 时不再经过任何矩阵，故空标量乘积为 $1$。由矩阵条目非负，其 $\ell^\infty$ 算子范数等于最大行和；每行至多含 $s_m$ 个非零条目，每个条目不超过 $\lambda_m$。因此，按 [推论 B.7](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-36ae8406e21d3213>)，

$$
\alpha_m
=\|\mathbf M^{(m)}\|_{\infty\to\infty}
\le s_m\lambda_m.
$$

所有因子非负，逐项代入上述有限乘积便得

$$
\|e^{(k)}\|_\infty
\le
\left(\prod_{t=1}^k s_t\lambda_t\right)\|e^{(0)}\|_\infty
+\sum_{m=1}^k
\left(\prod_{t=m+1}^k s_t\lambda_t\right)\|r^{(m)}\|_\infty.
$$

**(iii)** 固定 $x,y\in U_1$，令 $x_0=x$、$y_0=y$，并递归定义

$$
x_m=\phi_m(x_{m-1}),\qquad
y_m=\phi_m(y_{m-1}).
$$

由实际输入域的构造，$x_{m-1},y_{m-1}\in U_m\subseteq\operatorname{dom}(\phi_m)$。因此所有参与比较的点均为非吸收点，其坐标距离为有限实数。令

$$
e_j^{(m)}=|(x_m)_j-(y_m)_j|,
\qquad r^{(m)}=0.
$$

第 $m$ 步的合法 Lip 证书逐条目有限，因而按上述约定有

$$
e_j^{(m)}
\le\sum_{i\in I}M^{(m)}_{i\to j}e_i^{(m-1)}.
$$

这正是 (i) 的无余项递推。又有 $\|e^{(m)}\|_\infty=d_I(x_m,y_m)$，故由 (ii) 得到

$$
d_I(c_k(x),c_k(y))
\le
\left(\prod_{m=1}^k s_m\lambda_m\right)d_I(x,y).
$$

$\square$

</div>



### 有限维算子网络


<div data-mb-solution="oet-ffff5f45b5825156" data-mb-for="oet-b3f71b0e8b87fbf0">

**习题 C.1 的解答**：

**(i)** 首节点的两个转移域不交且穷尽其非吸收输出；后继节点立即终止，故每条入口轨迹均恰有两个节点。两个半方形均非空，因此所有三个节点都实际可达。可达路径只有

$$
p_-=(\alpha,\beta),\qquad p_+=(\alpha,\gamma),
$$

对应

$$
U_{p_-}=[-1,0)\times[-1,1],\qquad
U_{p_+}=[0,1]\times[-1,1].
$$

路径复合分别为 $c_{p_-}(s,t)=(s,0)$、$c_{p_+}(s,t)=(0,t)$，故

$$
\phi_{\mathcal N}(U)
=([-1,0)\times\{0\})\cup(\{0\}\times[-1,1]).
$$

**(ii)** 两条路径的线性部分分别是 $\operatorname{diag}(1,0)$ 与 $\operatorname{diag}(0,1)$，其像空间都是一维；它们都是非零正交投影，欧氏算子范数均为 $1$。各路径域均包含其所选中心的一个开邻域，故点差张成 $\mathbb R^2$，实际限制秩也均为 $1$。在任一路径域中，点与相应中心的横坐标差的绝对值不超过 $1/2$，纵坐标的偏差绝对值不超过 $1$，所以

$$
\|x-x_{p_\pm}\|_2^2\le\frac14+1=\frac54.
$$

两中心各自在对应路径域内，因而 $R=\sqrt5/2$ 满足覆盖命题的条件。逐路径代入后求和即得

$$
\mathcal N_{\mathrm{Euc}}(\varepsilon,\phi_{\mathcal N}(U))
\le\sum_{p\in\{p_-,p_+\}}
\left(1+\frac{2\cdot1\cdot(\sqrt5/2)}{\varepsilon}\right)^1
=2\left(1+\frac{\sqrt5}{\varepsilon}\right).
$$

该指数来自每条路径线性像的维数：输入域虽然是二维的，每条路径的输出却被限制在一条直线上。$\square$

</div>



<div data-mb-solution="oet-d3860e268be11fe1" data-mb-for="oet-84ef8daaa0e28176">

**习题 C.2 的解答**：

**(i)** 对 $(s,0)\in U$，有 $F(s,0)=G(s,0)=(s,0)$。两扩展的导数分别为

$$
DF=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
DG=\begin{pmatrix}1&0\\0&1\end{pmatrix},
$$

故秩分别为 $1$、$2$。

**(ii)** 域内点差均为 $(a,0)$，且包含一个非零横向向量，故

$$
W_U=\mathbb R\times\{0\}.
$$

$DF$ 与 $DG$ 在这个空间上都把 $(a,0)$ 映为 $(a,0)$，因此两个限制映射相同，秩均为 $1$。由 [推论 C.7](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-c9e4b6fb4f7e4e59>) 得到的覆盖指数均为 $1$；二者的全空间算子范数也都为 $1$，所以取相同中心、半径时给出相同上界。共同输出集合为 $F(U)=G(U)=U$。

若改用整个矩阵的秩，两个指数会分别为 $1$ 与 $2$，后一估计仍有效但较宽。实际路径域未包含的第二坐标方向的变化影响扩展矩阵的秩，却不改变 [引理 B.13](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-5327d971cf04c4ca>) 所确定的受限秩。$\square$

</div>



<div data-mb-solution="oet-cf84f3e370e7d17c" data-mb-for="oet-64877d77e522a25b">

**习题 C.3 的解答**：

**(i)** 对 [推论 C.2](<appendix-c-finite-dimensional-operator-networks.md#user-content-oet-f8dabd5aec160cd3>) 证明中的有限和使用三角不等式，再对每个通路项逐次使用欧氏算子范数的次乘性，得到

$$
\begin{aligned}
&\|P_{a_r}\circ DC_p(x)\circ P_{a_0}\|_{2\to2}\\
&\quad\le
\sum_{a_1,\ldots,a_{r-1}\in H}
\bigl\|\bigl(P_{a_r}\circ A_{p,r}(x)\circ P_{a_{r-1}}\bigr)\circ\cdots\circ
\bigl(P_{a_1}\circ A_{p,1}(x)\circ P_{a_0}\bigr)\bigr\|_{2\to2}\\
&\quad\le
\sum_{a_1,\ldots,a_{r-1}\in H}
\prod_{s=1}^r
\|P_{a_s}\circ A_{p,s}(x)\circ P_{a_{s-1}}\|_{2\to2}.
\end{aligned}
$$

相邻块因子复合时，重复的投影由 $P_a^2=P_a$ 合并，故每个通路项正是这些块映射的复合。当 $r=1$ 时，上式只有一项，结论也成立。

**(ii)** 单块分解的投影为 $P_1=I_2$。由于 $A\ne0$、$B\ne0$，两步各自的唯一块映射均非零，存在块指标通路 $1\to1\to1$。但是

$$
BA=\begin{pmatrix}0&0\\0&0\end{pmatrix},
$$

所以复合映射及其唯一块映射均为零。另一方面，

$$
\operatorname{im}(A)=\mathbb R\times\{0\}=\ker(B),
$$

这解释了 $BA=0$。这里没有不同通路之间的相消：唯一通路上的两个非零块映射，其复合本身就是零。逐步非零条件没有记录前一步像空间与后一步核空间的相对位置。$\square$

</div>



<div data-mb-solution="oet-a53439ed4ddb2041" data-mb-for="oet-b3af1b7e2f078cb4">

**习题 C.4 的解答**：

**(i)** 域内点差均与 $(1,1)$ 共线，且存在非零点差，所以

$$
W_{D_q^{\mathrm{in}}}=\operatorname{span}\{(1,1)\}.
$$

节点矩阵的两行分别为 $(1,-1)$ 与 $(1,1)$。第一行在该方向空间上为零，第二行不为零；直接代入也得到

$$
f_q(t,t)=(0,2t)\qquad(-1\le t\le1).
$$

因此常值分量集合恰为 $\{1\}$。第一行虽然非零，但实际域只允许沿对角线变化，而该行在这个方向上消失。

**(ii)** 两个输入坐标的取值范围均为 $[-1,1]$，直径均为 $2$。该发生域非空且凸，由 [命题 B.14](<appendix-b-finite-dimensional-coordinate-model.md#user-content-oet-055e3702cf9c3930>) 的 (ii)，对任意 $i\in\{1,2\}$ 有

$$
\underline{r}^{\mathrm N}_q(i,1)=+\infty,
\qquad
\underline{r}^{\mathrm N}_q(i,2)=0.
$$

取两个阈值均为 $1$，按照 [§ 5.5](<05-operator-networks.md#user-content-oet-4b1389b158d2780e>) 的定义得到

$$
\operatorname{Type}_q(i,1)=(0,1),
\qquad
\operatorname{Type}_q(i,2)=(0,0).
$$

发生域在 $\mathbb R^2$ 中没有内点，不能把受限行的零性替换为整行的零性；否则会误判第一个输出分量。$\square$

</div>
