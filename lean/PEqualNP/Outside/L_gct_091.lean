import PEqualNP.Defs
namespace PEqualNP.Outside.L_gct_091
abbrev KD:=ℂ
section
open Module Finset Submodule Matrix Pi Fin Equiv
abbrev ze:=Fin 4 × Fin 4->KD
variable {L:Submodule KD ze}
abbrev zx:=Fin 3 -> Fin 3->KD
def z6:Fin 3 -> Fin 2 -> Fin 3:=![![1,2],![0,2],![0,1]]
abbrev zV:=z6
def z8:Fin 4 -> Fin 3 -> Fin 4:=![![1,2,3],![0,2,3],![0,1,3],![0,1,2]]
def Kg (X:Fin 2 -> Fin 2->KD):KD:=X 0 0*X 1 1+X 0 1*X 1 0
def zn (A:zx):zx:=λ i j=>Kg λ a b=>A (z6 i a) (z6 j b)
def zp (A B:zx):zx:=λ i j=>zn (A+B) i j-zn A i j-zn B i j
def zo (A:zx):KD:=∑ j,A 0 j*zn A 0 j
def ql (X:Fin 4 -> Fin 4->KD):KD :=
 ∑ j,X 0 j*zo λ a b=>X (z8 0 a) (z8 j b)
def qk:ze:=λ _=>1
def qY (T:ze):KD:=∑ p,T p
noncomputable def yl (T:ze):KD :=
 ((∑ p,T p)^2-∑ i,(∑ j,T (i,j))^2-∑ j,(∑ i,T (i,j))^2+∑ p,T p^2)/2
def jh (T:ze):KD:=∑ i,∑ j,zo λ a b=>T (z8 i a,z8 j b)
def k8 (T:ze):KD:=ql λ i j=>T (i,j)
def zg (L:Submodule KD ze):Prop :=
 ∀ t∈L,ql (λ i j=>1+t (i,j))=24
lemma zs (A:zx):zo A=A 0 0*(A 1 1*A 2 2+A 1 2*A 2 1)+A 0 1*(A 1 0*A 2 2+A 1 2*A 2 0)+A 0 2*(A 1 0*A 2 1+A 1 1*A 2 0):=by simp[zo,zn,Kg,z6,sum_univ_three]
lemma zK (A:zx) (i j:Fin 3):zn A i j=A (z6 i 0) (z6 j 0)*A (z6 i 1) (z6 j 1)+A (z6 i 0) (z6 j 1)*A (z6 i 1) (z6 j 0):=rfl
lemma zY (X:Fin 4 -> Fin 4->KD):ql X=X 0 0*zo ![![X 1 1,X 1 2,X 1 3],![X 2 1,X 2 2,X 2 3],![X 3 1,X 3 2,X 3 3]]+X 0 1*zo ![![X 1 0,X 1 2,X 1 3],![X 2 0,X 2 2,X 2 3],![X 3 0,X 3 2,X 3 3]]+X 0 2*zo ![![X 1 0,X 1 1,X 1 3],![X 2 0,X 2 1,X 2 3],![X 3 0,X 3 1,X 3 3]]+X 0 3*zo ![![X 1 0,X 1 1,X 1 2],![X 2 0,X 2 1,X 2 2],![X 3 0,X 3 1,X 3 2]]:=by simp only[ql,zs,sum_univ_four];simp[z8]
lemma yd (X:Fin 4 -> Fin 4->KD) (i:Fin 4):ql X=∑ j,X i j*zo λ a b=>X (z8 i a) (z8 j b):=by rw[zY];fin_cases i<;>simp[zs,z8,sum_univ_four]<;>ring
lemma ye (X:Fin 4 -> Fin 4->KD) (j:Fin 4):ql X=∑ i,X i j*zo λ a b=>X (z8 i a) (z8 j b):=by rw[zY];fin_cases j<;>simp[zs,z8,sum_univ_four]<;>ring
lemma wJ (X:Fin 4 -> Fin 4->KD):ql X=X 0 0*zo (λ a b=>X a.succ b.succ)+∑ a,∑ b,X a.succ 0*zn (λ a b=>X a.succ b.succ) a b*X 0 b.succ:=by rw[zY];simp[zs,zK,z6,sum_univ_three];ring
lemma jb (A:zx) (i:Fin 3):zo A=∑ j,A i j*zn A i j:=by rw[zs];fin_cases i<;>simp[zK,z6,sum_univ_three]<;>ring
lemma jc (A:zx) (j:Fin 3):zo A=∑ i,A i j*zn A i j:=by rw[zs];fin_cases j<;>simp[zK,z6,sum_univ_three]<;>ring
lemma Wi {n:ℕ} (g:Perm (Fin (n+1))->KD):∑ σ,g σ=∑ a:Fin (n+1),∑ τ:Perm (Fin n),g (Perm.decomposeFin.symm (a,τ)):=by rw[←Perm.decomposeFin.symm.sum_comp,Fintype.sum_prod_type]
lemma Qp (X:Fin 4 -> Fin 4->KD):ql X=(of X).permanent:=by simp only[permanent,Wi (n:=3),Wi (n:=2),Wi (n:=1),Wi (n:=0)];simp only[sum_univ_succ,sum_univ_zero,prod_univ_succ,prod_univ_zero,Perm.decomposeFin_symm_apply_zero,Perm.decomposeFin_symm_apply_succ,Fintype.sum_unique];simp +decide [swap_apply_def,zY,zs];ring
lemma Kv (z:Fin 4 × Fin 4->KD):MvPolynomial.eval z (PEqualNP.Gct.permPoly KD 4)=ql λ i j=>z (i,j):=by rw[Qp];simp[PEqualNP.Gct.permPoly,permanent,mvPolynomialX_apply]
lemma jN (h:∀ t∈L,MvPolynomial.eval (λ p=>1+t p) (PEqualNP.Gct.permPoly KD 4)=(Nat.factorial 4:KD)):zg L:=λ t a=>by have:=h t a;rw[Kv] at this;rw[this];simp[Nat.factorial]
lemma Kh (a z:KD) (T:ze):ql (λ i j=>a+z*T (i,j))=24*a^4+6*a^3*z*qY T+2*a^2*z^2*yl T+a*z^3*jh T+z^4*k8 T:=by simp only[qY,yl,jh,k8,zY,zs,Fintype.sum_prod_type,sum_univ_four];simp[z8];ring
lemma qD (c0 c1 c2 c3 c4:KD) (h:∀ z:KD,c0+c1*z+c2*z^2+c3*z^3+c4*z^4=0):c0=0/\c1=0/\c2=0/\c3=0/\c4=0:=⟨by linear_combination h 0,by linear_combination (2/3:KD)*h 1-(2/3:KD)*h (-1)-(1/12:KD)*h 2+(1/12:KD)*h (-2),by linear_combination (-5/4:KD)*h 0+(2/3:KD)*h 1+(2/3:KD)*h (-1)-(1/24:KD)*h 2-(1/24:KD)*h (-2),by linear_combination (-1/6:KD)*h 1+(1/6:KD)*h (-1)+(1/12:KD)*h 2-(1/12:KD)*h (-2),by linear_combination (1/4:KD)*h 0-(1/6:KD)*h 1-(1/6:KD)*h (-1)+(1/24:KD)*h 2+(1/24:KD)*h (-2)⟩
lemma qE (c0 c1 c2 c3:KD) (h:∀ z:KD,c0+c1*z+c2*z^2+c3*z^3=0):c0=0/\c1=0/\c2=0/\c3=0:=let e:=qD c0 c1 c2 c3 0 λ z=>by linear_combination h z
 ⟨e.1,e.2.1,e.2.2.1,e.2.2.2.1⟩
lemma qc (c0 c1 c2:KD) (h:∀ z:KD,c0+c1*z+c2*z^2=0):c0=0/\c1=0/\c2=0:=let e:=qD c0 c1 c2 0 0 λ z=>by linear_combination h z
 ⟨e.1,e.2.1,e.2.2.1⟩
def z9 (i:Fin 4):ze →ₗ[KD] Fin 4->KD:=LinearMap.pi λ j=>LinearMap.proj (i,j)
def zD (j:Fin 4):ze →ₗ[KD] Fin 4->KD:=LinearMap.pi λ i=>LinearMap.proj (i,j)
def z7 (i j:Fin 4):ze →ₗ[KD] zx :=
 LinearMap.pi λ a=>LinearMap.pi λ b=>LinearMap.proj (z8 i a,z8 j b)
abbrev qZ:=z7 0 0
def zh (L:Submodule KD ze) (i:Fin 4):Submodule KD ze:=L⊓LinearMap.ker (z9 i)
def zC (L:Submodule KD ze) (j:Fin 4):Submodule KD ze:=L⊓LinearMap.ker (zD j)
def zm (L:Submodule KD ze) (i j:Fin 4):Submodule KD ze:=zh L i⊓zC L j
lemma zA (i j:Fin 4) (X:ze):z9 i X j=X (i,j):=rfl
lemma qF (i j:Fin 4) (X:ze):zD j X i=X (i,j):=rfl
lemma zt (i j:Fin 4) (X:ze) (a b:Fin 3):z7 i j X a b=X (z8 i a,z8 j b):=rfl
open LinearMap in
lemma zW {E F:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] [AddCommGroup F] [Module KD F] (f:E →ₗ[KD] F) (N:Submodule KD E):finrank KD (N.map f)+finrank KD (N⊓ker f:Submodule KD E)=finrank KD N:=by rw[←(f.domRestrict N).finrank_range_add_finrank_ker,range_domRestrict,ker_domRestrict,←(comapSubtypeEquivOfLe (inf_le_left:N⊓ker f≤N)).finrank_eq,comap_inf,comap_subtype_self,top_inf_eq]
lemma jV {E:Type} [AddCommGroup E] [Module KD E] (L:Submodule KD E) {n:ℕ} [FiniteDimensional KD L] (h:n≤finrank KD L):∃ L'≤L,finrank KD L'=n:=by
 have⟨f,a⟩:=exists_linearIndependent_of_le_finrank h;refine⟨span KD (Set.range λ k=>(f k:E)),span_le.2 ?_,?_⟩
 . rintro _ ⟨k,rfl⟩;exact(f k).2
 . exact(finrank_span_eq_card (a.map' L.subtype (ker_subtype L))).trans (by simp)
lemma wK (P:Submodule KD (Fin 4->KD)) (h:(λ _=>(1:KD))∉P):finrank KD P≤3:=by have:=finrank_lt (s:=P) λ e=>h (e ▸ mem_top);simp at this;omega
lemma qb (hL:zg L) {T:ze} (hT:T∈L):qY T=0/\yl T=0/\jh T=0/\k8 T=0:=by
 obtain⟨-,a,b,c,d⟩:=qD 0 (6*qY T) (2*yl T) (jh T) (k8 T) λ z=>by have e:=hL _ (L.smul_mem z hT);simp only[Pi.smul_apply,smul_eq_mul] at e;linear_combination e-Kh 1 z T
 grind
lemma qP (hL:zg L) {T:ze} (hT:T∈L) (a:KD):ql (λ i j=>a+T (i,j))=24*a^4:=by have⟨b,c,d,e⟩:=qb hL hT;have:=Kh a 1 T;simp only[one_mul] at this;rw[this,b,c,d,e];ring
lemma ku (hL:zg L):qk∉L:=λ h=>by have:=hL _ (L.neg_mem h);simp[qk,zY,zs] at this
lemma qg (hL:zg L) (i:Fin 4):(λ _=>(1:KD))∉L.map (z9 i):=by rintro⟨T,a,b⟩;have:=hL _ (L.neg_mem a);rw[yd _ i] at this;have c:∀ j,T (i,j)=1:=λ j=>congrFun b j;simp[c] at this
lemma jz (hL:zg L) (j:Fin 4):(λ _=>(1:KD))∉L.map (zD j):=by rintro⟨T,a,b⟩;have:=hL _ (L.neg_mem a);rw[ye _ j] at this;have c:∀ i,T (i,j)=1:=λ i=>congrFun b i;simp[c] at this
lemma yq (hL:zg L) (i:Fin 4):finrank KD (L.map (z9 i))≤3:=wK _ (qg hL i)
lemma k9 (hL:zg L) (j:Fin 4):finrank KD (L.map (zD j))≤3:=wK _ (jz hL j)
lemma Kw (P:Submodule KD (Fin 4->KD)) (i:(λ _=>(1:KD))∉P) (r:finrank KD P=3):(∀ v,∃ a:KD,∃ y∈P,v=a•(λ _=>(1:KD))+y)/\∃ l:(Fin 4->KD) →ₗ[KD] KD,l (λ _=>1)=1/\(∀ y∈P,l y=0)/\∀ m:(Fin 4->KD) →ₗ[KD] KD,m (λ _=>1)=1->(∀ y∈P,m y=0) -> m=l:=by
 have g:∀ v,∃ a:KD,∃ y∈P,v=a•(λ _=>(1:KD))+y:=by
  have d:P⊔span KD {λ _=>(1:KD)}=⊤:=by apply eq_top_of_finrank_eq;have q:=finrank_lt_finrank_of_lt (lt_of_le_of_ne (le_sup_left:P≤P⊔span KD {λ _=>(1:KD)}) λ e=>i (by rw[e];exact mem_sup_right (mem_span_singleton_self _)));have j:=finrank_le (P⊔span KD {λ _=>(1:KD)});simp only[finrank_fin_fun] at j⊢;omega
  intro v;obtain⟨y,b,w,k,rfl⟩:=Submodule.mem_sup.1 (d ▸ mem_top:v∈P⊔_);obtain⟨a,rfl⟩:=mem_span_singleton.1 k;grind
 have⟨f,n,o⟩:=exists_dual_map_eq_bot_of_notMem i inferInstance;have c:∀ y∈P,f y=0:=λ y b=>by have:f y∈P.map f:=⟨y,b,rfl⟩;rw[o] at this;simpa using this
 refine⟨g,(f λ _=>1)⁻¹•f,by simp[n],λ y b=>by simp[c y b],λ m p h=>LinearMap.ext λ v=>?_⟩;obtain⟨a,y,b,rfl⟩:=g v;simp[p,h y b,c y b];field_simp
lemma Ki (R:ze →ₗ[KD] Fin 4->KD) (g:(λ _=>(1:KD))∉L.map R) (h:finrank KD (L.map R)=3):(∀ v:Fin 4->KD,∃ a:KD,∃ T∈L,v=λ j=>a+R T j)/\∃ l:(Fin 4->KD) →ₗ[KD] KD,(∀ a,∀ T∈L,l (λ j=>a+R T j)=a)/\∀ m:(Fin 4->KD) →ₗ[KD] KD,(∀ a,∀ T∈L,m (λ j=>a+R T j)=a) -> m=l:=by
 obtain⟨i,l,k,n,-⟩:=Kw _ g h;have e:∀ a T,(λ j=>a+R T j)=a•(λ _=>(1:KD))+R T:=λ a T=>by funext j;simp
 have b:∀ v:Fin 4->KD,∃ a:KD,∃ T∈L,v=λ j=>a+R T j:=by simp_all
 have c:∀ a,∀ T∈L,l (λ j=>a+R T j)=a:=by simp_all
 refine⟨b,l,c,λ m f=>LinearMap.ext λ v=>?_⟩;obtain⟨a,T,d,rfl⟩:=b v;rw[f a T d,c a T d]
lemma qu (hL:zg L) {i:Fin 4} (h3:finrank KD (L.map (z9 i))=3):(∀ v:Fin 4->KD,∃ a:KD,∃ T∈L,v=λ j=>a+T (i,j))/\∃ l:(Fin 4->KD) →ₗ[KD] KD,(∀ a,∀ T∈L,l (λ j=>a+T (i,j))=a)/\∀ m:(Fin 4->KD) →ₗ[KD] KD,(∀ a,∀ T∈L,m (λ j=>a+T (i,j))=a) -> m=l:=Ki _ (qg hL i) h3
lemma j3 (hL:zg L) {j:Fin 4} (h3:finrank KD (L.map (zD j))=3):(∀ v:Fin 4->KD,∃ a:KD,∃ T∈L,v=λ i=>a+T (i,j))/\∃ l:(Fin 4->KD) →ₗ[KD] KD,(∀ a,∀ T∈L,l (λ i=>a+T (i,j))=a)/\∀ m:(Fin 4->KD) →ₗ[KD] KD,(∀ a,∀ T∈L,m (λ i=>a+T (i,j))=a) -> m=l:=Ki _ (jz hL j) h3
def qm (A B:zx):KD:=∑ i,∑ j,B i j*zn A i j
lemma ji (a z:KD) (A B:zx):zo (λ i j=>a*A i j+z*B i j)=a^3*zo A+a^2*z*qm A B+a*z^2*qm B A+z^3*zo B:=by simp only[zs,qm,zK,sum_univ_three];simp[z6];ring
lemma zR (A B:zx) (i j:Fin 3):zp A B i j=A (z6 i 0) (z6 j 0)*B (z6 i 1) (z6 j 1)+B (z6 i 0) (z6 j 0)*A (z6 i 1) (z6 j 1)+A (z6 i 0) (z6 j 1)*B (z6 i 1) (z6 j 0)+B (z6 i 0) (z6 j 1)*A (z6 i 1) (z6 j 0):=by simp only[zp,zK,Pi.add_apply];ring
lemma qr {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (B:V →ₗ[KD] V →ₗ[KD] KD) (U W:Submodule KD V) (hUW:∀ x∈U,∀ y∈W,B x y=0):finrank KD U+finrank KD W≤finrank KD V+finrank KD (U⊓LinearMap.ker B:Submodule KD V):=by have c:=zW B U;have d:finrank KD W+finrank KD W.dualAnnihilator=finrank KD V:=Subspace.finrank_add_finrank_dualAnnihilator_eq W;have e:finrank KD (U.map B)≤finrank KD W.dualAnnihilator:=finrank_mono (by rintro _ ⟨x,a,rfl⟩;exact(mem_dualAnnihilator _).2 λ y b=>hUW x a y b);omega
open LinearMap in
lemma Kj {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (B:V →ₗ[KD] V →ₗ[KD] KD) {k:ℕ} (w v:Fin k -> V) (c:∀ a b,B (w a) (v b)=if a=b then 1 else 0):finrank KD (ker B)+k≤finrank KD V:=by let φ:V →ₗ[KD] Fin k->KD:=LinearMap.pi λ b=>B.flip (v b);have d:LinearMap.range φ=⊤:=range_eq_top.2 λ u=>⟨∑ a,u a•w a,funext λ b=>by simp[φ,c]⟩;have h:=φ.finrank_range_add_finrank_ker;rw[d,finrank_top,finrank_fin_fun] at h;have:=finrank_mono (show ker B≤ker φ from λ x e=>funext λ b=>by simp[φ,mem_ker.1 e]);omega
lemma Kk {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (B:V →ₗ[KD] V →ₗ[KD] KD) (U W:Submodule KD V) (c:∀ x∈U,∀ y∈W,B x y=0) {k:ℕ} (w v:Fin k -> V) (d:∀ a b,B (w a) (v b)=if a=b then 1 else 0):finrank KD U+finrank KD W+k≤2*finrank KD V:=by have:=qr B U W c;have:=Kj B w v d;have:=finrank_mono (inf_le_right:U⊓LinearMap.ker B≤_);omega
lemma yr {V:Type} [AddCommGroup V] [Module KD V] (B:V →ₗ[KD] V →ₗ[KD] KD) (hs:∀ x y,B x y=B y x) (U:Submodule KD V) (h:∀ x∈U,B x x=0):∀ x∈U,∀ y∈U,B x y=0:=λ x a y b=>by have:=h _ (U.add_mem a b);simp only[map_add,LinearMap.add_apply] at this;grind
lemma zz {E:Type} [AddCommGroup E] [Module KD E] (N:Submodule KD E) (f g:E →ₗ[KD] KD) (h:∀ x∈N,f x*g x=0):(∀ x∈N,f x=0)\/∀ x∈N,g x=0:=by by_contra! a;have⟨⟨x,b,c⟩,y,d,e⟩:=a;have i:=(mul_eq_zero.1 (h x b)).resolve_left c;have j:=(mul_eq_zero.1 (h y d)).resolve_right e;have:=h _ (N.add_mem b d);simp[i,j,c,e] at this
def zq (p q:Perm (Fin 4)):ze ≃ₗ[KD] ze :=
 LinearEquiv.funCongrLeft KD KD (prodCongr p q)
def zM:ze ≃ₗ[KD] ze:=LinearEquiv.funCongrLeft KD KD (prodComm _ _)
lemma zy (p q:Perm (Fin 4)) (X:ze) (i j:Fin 4):zq p q X (i,j)=X (p i,q j):=rfl
lemma zQ (X:ze) (i j:Fin 4):zM X (i,j)=X (j,i):=rfl
lemma Kx (p q:Perm (Fin 4)) (X:Fin 4 -> Fin 4->KD):ql (λ i j=>X (p i) (q j))=ql X:=by rw[Qp,Qp];have:of (λ i j=>X (p i) (q j))=((of X).submatrix p id).submatrix id q:=rfl;rw[this,permanent_permute_rows,permanent_permute_cols]
lemma Wm (X:Fin 4 -> Fin 4->KD):ql (λ i j=>X j i)=ql X:=by rw[Qp,Qp];exact(congrArg permanent (rfl:of (λ i j=>X j i)=(of X).transpose)).trans (permanent_transpose _)
lemma zH (hL:zg L) (p q:Perm (Fin 4)):zg (L.map (zq p q:ze →ₗ[KD] ze)):=by rintro _ ⟨X,a,rfl⟩;exact(Kx p q (λ i j=>1+X (i,j))).trans (hL X a)
lemma zX (hL:zg L):zg (L.map (zM:ze →ₗ[KD] ze)):=by rintro _ ⟨X,a,rfl⟩;exact(Wm (λ i j=>1+X (i,j))).trans (hL X a)
lemma zF (L:Submodule KD ze) (p q:Perm (Fin 4)):finrank KD (L.map (zq p q:ze →ₗ[KD] ze))=finrank KD L:=LinearEquiv.finrank_map_eq _ _
lemma zT (L:Submodule KD ze):finrank KD (L.map (zM:ze →ₗ[KD] ze))=finrank KD L:=LinearEquiv.finrank_map_eq _ _
lemma qC {X Y:Type} [AddCommGroup X] [Module KD X] [AddCommGroup Y] [Module KD Y] (β:X →ₗ[KD] Y →ₗ[KD] KD) (f:X →ₗ[KD] KD) (g:Y →ₗ[KD] KD) {x0:X} {y0:Y} (hx:f x0=1) (hy:g y0=1) (h:∀ x y,f x=g y->β x y=0):∀ x y,β x y=0:=by intro x y;have a:=h (x-f x•x0) (y-g y•y0) (by simp[hx,hy]);have d:=h x0 y0 (by rw[hx,hy]);have b:=h x0 (y0+(y-g y•y0)) (by simp[hx,hy]);have c:=h (x0+(x-f x•x0)) y0 (by simp[hx,hy]);simp only[map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul] at a b c;grind
lemma yF {E:Type} [AddCommGroup E] [Module KD E] (N:Submodule KD E) (u1 u2 L1 L2:E →ₗ[KD] KD) {e1 e2:E} (he1:e1∈N) (he2:e2∈N) (h11:u1 e1=1) (h21:u2 e1=0) (h12:u1 e2=0) (h22:u2 e2=1) (h:∀ x∈N,u1 x*L2 x+u2 x*L1 x=0):∃ κ:KD,∀ x∈N,L2 x=κ*u2 x/\L1 x = -κ*u1 x:=by
 have P:∀ x∈N,∀ y∈N,u1 x*L2 y+u1 y*L2 x+u2 x*L1 y+u2 y*L1 x=0:=λ x a y b=>by have:=h _ (N.add_mem a b);simp only[map_add] at this;grind
 have c:=h e1 he1;have d:=h e2 he2;have e:=P e1 he1 e2 he2;rw[h11,h21] at c;rw[h12,h22] at d;rw[h11,h12,h21,h22] at e;refine⟨L2 e2,λ x a=>⟨?_,?_⟩⟩<;>grind
lemma Wn (a r0 p s Q R:KD) (b:a*r0=24) (c:a*s+p*r0=0) (d:a*R+p*s+Q*r0=0) (e:p*R+Q*s=0) (f:Q*R=0):Q=0/\R=0/\p=0/\s=0:=by grind
lemma jG {E:Type} [AddCommGroup E] [Module KD E] (N:Submodule KD E) (Bq Br:E →ₗ[KD] E →ₗ[KD] KD) (α:E →ₗ[KD] KD) {e:E} (he:e∈N) (hα:α e=1) (h:∀ x∈N,Bq x x*Br x x=24*α x^4):∃ c:KD,c≠0/\∀ x∈N,Bq x x=c*α x^2/\Br x x=24/c*α x^2:=by
 have d:=h e he;rw[hα,one_pow,mul_one] at d;have g:Bq e e≠0:=λ n=>by grind
 refine⟨Bq e e,g,λ x i=>?_⟩;obtain⟨a,z,f,b,rfl⟩:∃ a:KD,∃ z∈N,α z=0/\x=a•e+z:=⟨α x,x-α x•e,N.sub_mem i (N.smul_mem _ he),by simp[hα],by simp⟩;obtain⟨-,j,k,l,m⟩:=qD (Bq e e*Br e e-24) (Bq e e*(Br e z+Br z e)+(Bq e z+Bq z e)*Br e e) (Bq e e*Br z z+(Bq e z+Bq z e)*(Br e z+Br z e)+Bq z z*Br e e) ((Bq e z+Bq z e)*Br z z+Bq z z*(Br e z+Br z e)) (Bq z z*Br z z) λ t=>by have:=h _ (N.add_mem he (N.smul_mem t f));simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hα,b] at this;linear_combination this
 have⟨o,p,q,r⟩:=Wn _ _ _ _ _ _ d j k l m;simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hα,b];grind
lemma Wo {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (B:V →ₗ[KD] V →ₗ[KD] KD) (U:Submodule KD V) {b:V} (e:∀ x∈U,∀ y∈U,B x y=0) (k:∀ x∈U,B x b=0) (f:B b b≠0):2*finrank KD U+1≤finrank KD V+finrank KD (U⊓LinearMap.ker B:Submodule KD V):=by
 have h:=qr B U (U⊔span KD {b}) λ x a y g=>by obtain⟨u,i,w,j,rfl⟩:=Submodule.mem_sup.1 g;obtain⟨c,rfl⟩:=mem_span_singleton.1 j;simp[e x a u i,k x a]
 have:=finrank_lt_finrank_of_lt (IsConcreteLE.lt_iff_le_and_exists.2 ⟨le_sup_left,b,mem_sup_right (mem_span_singleton_self b),λ d=>f (e b d b d)⟩);omega
abbrev vl:=(Fin 3->KD) × (Fin 3->KD)
@[simp] def gE14 (w u v:Fin 3->KD):KD :=
 w 2*(u 0*v 1+u 1*v 0)+w 1*(u 0*v 2+u 2*v 0)+w 0*(u 1*v 2+u 2*v 1)
@[simp] def gE15 (w:Fin 3->KD):vl →ₗ[KD] vl →ₗ[KD] KD:=by
 refine LinearMap.mk₂ KD (λ x y=>gE14 w x.1 y.2+gE14 w y.1 x.2) ?_ ?_ ?_ ?_ <;>
  intros<;>simp<;>ring
lemma Wp (w:Fin 3->KD) (c:Fin 3) (a:w c≠0):finrank KD (gE15 w).ker+4≤6:=by
 have h:=Kj (gE15 w) ![(Pi.single (z6 c 0) 1,0),(Pi.single (z6 c 1) 1,0),(0,Pi.single (z6 c 0) 1),(0,Pi.single (z6 c 1) 1)] ![(0,Pi.single (z6 c 1) (w c)⁻¹),(0,Pi.single (z6 c 0) (w c)⁻¹),(Pi.single (z6 c 1) (w c)⁻¹,0),(Pi.single (z6 c 0) (w c)⁻¹,0)] λ i j=>by fin_cases c<;>simp at a<;>fin_cases i<;>fin_cases j<;>simp[z6,a]
 simpa using h
lemma Wq (w:Fin 3->KD) (x:vl) (i:Fin 3):w i*gE15 w x (0,λ j=>if j=i then -w j else w j)=2*(w 0*w 1*w 2)*x.1 i/\w i*gE15 w x (λ j=>if j=i then -w j else w j,0)=2*(w 0*w 1*w 2)*x.2 i:=by fin_cases i<;>simp<;>constructor<;>ring
open LinearMap in
open Submodule in
theorem jH (B:zx) (N:Submodule KD zx) (h3:finrank KD N=3) (h0:∀ T∈N,∀ b,T 0 b=0) (hB:zo B≠0) (hN:∀ T∈N,zo (B+T)=zo B):(B 0 0=0\/B 0 1=0\/B 0 2=0)/\∀ n:Fin 3->KD,B 0 2*n 1+B 0 1*n 2=0 -> B 0 2*n 0+B 0 0*n 2=0 -> B 0 1*n 0+B 0 0*n 1=0->(λ a b=>if a=1 then n b else 0)∈N/\(λ a b=>if a=2 then n b else 0)∈N:=by
 have⟨c,hc⟩:∃ c,B 0 c≠0:=by by_contra! h;exact hB (by simp[zs,h])
 have hrad:=Wp (B 0) c hc;set F:=gE15 (B 0);let p:zx →ₗ[KD] vl:=(proj 1).prod (proj 2);have key:∀ T∈N,F (p T) (p B)=0/\F (p T) (p T)=0:=λ T hT=>by
  obtain⟨-,h1,h2⟩:=qc 0 (F (p T) (p B)) (F (p T) (p T)/2) λ t=>by have e:=hN _ (N.smul_mem t hT);simp[zs,h0 T hT,F,p] at e⊢;linear_combination e
  grind
 have hs:∀ x y,F x y=F y x:=λ _ _=>add_comm _ _;have h2:=finrank_sup_add_finrank_inf_eq (N.map p) F.ker;have h5:=finrank_mono (inf_le_right:N.map p⊓F.ker≤_);set U:=N.map p⊔F.ker;have hU:∀ x∈U,F x x=0/\F x (p B)=0:=λ x hx=>by obtain⟨_,⟨T,hT,rfl⟩,k,hk,rfl⟩:=mem_sup.1 hx;rw[mem_ker] at hk;simp[hk,hs (p T) k,key T hT]
 have hiso:=yr F hs U λ x hx=>(hU x hx).1;set W:=U⊔span KD {p B};have h1:=qr F U W λ x hx y hy=>by obtain⟨u,hu,_,hv,rfl⟩:=mem_sup.1 hy;obtain⟨a,rfl⟩:=mem_span_singleton.1 hv;simp[hiso x hx u hu,(hU x hx).2]
 have h4:=finrank_mono (inf_le_right:U⊓F.ker≤_);have hlt:finrank KD U<finrank KD W:=finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left λ e=>hB (by have:=(hU (p B) (e ▸ mem_sup_right (mem_span_singleton_self _))).1;rw[zs];simp[F,p] at this;linear_combination this));have inj:∀ T∈N,∀ X:zx,X 0=0 -> p T=p X -> T=X:=λ T hT X h e=>by funext a;fin_cases a;exacts[(funext (h0 T hT)).trans h.symm,congrArg Prod.fst e,congrArg Prod.snd e]
 have hN3:=zW p N;rw[(Submodule.eq_bot_iff (N⊓p.ker)).2 λ T ⟨hT,hk⟩=>inj T hT 0 rfl (mem_ker.1 hk),finrank_bot,h3] at hN3;have hV:finrank KD vl=6:=by simp
 have hKN:F.ker≤N.map p:=inf_eq_right.1 (eq_of_le_of_finrank_le inf_le_right (by omega));refine⟨?_,λ n e1 e2 e3=>?_⟩
 . by_contra hw;simp only[not_or] at hw
   have⟨x,hx,hx0⟩:=exists_mem_ne_zero_of_ne_bot λ h:F.ker=⊥=>by rw[←finrank_eq_zero] at h;omega
   have:=λ i=>Wq (B 0) x i;have t:∀ y,gE15 (B 0) x y=0:=LinearMap.congr_fun (mem_ker.1 hx);simp only[t] at this;simp[hw] at this;exact hx0 (Prod.ext (funext λ i=>(this i).1) (funext λ i=>(this i).2))
 . have lift:∀ X:zx,X 0=0->(∀ y,F (p X) y=0) -> X∈N:=λ X h hX=>let ⟨T,hT,e⟩:=hKN (mem_ker.2 (LinearMap.ext hX:F (p X)=0))
    inj T hT X h e ▸ hT
   exact⟨lift _ (funext λ _=>rfl) λ y=>by
    simp[F,p];linear_combination y.2 0*e1+y.2 1*e2+y.2 2*e3,
    lift _ (funext λ _=>rfl) λ y=>by
    simp[F,p];linear_combination y.1 0*e1+y.1 1*e2+y.1 2*e3⟩
open LinearMap in
lemma jO (B:zx) (N:Submodule KD zx) (h3:finrank KD N=3) (h0:∀ T∈N,∀ b,T b 0=0) (hB:zo B≠0) (hN:∀ T∈N,zo (B+T)=zo B):(B 0 0=0\/B 1 0=0\/B 2 0=0)/\∀ n:Fin 3->KD,B 2 0*n 1+B 1 0*n 2=0 -> B 2 0*n 0+B 0 0*n 2=0 -> B 1 0*n 0+B 0 0*n 1=0->(λ a b=>if b=1 then n a else 0)∈N/\(λ a b=>if b=2 then n a else 0)∈N:=by
 have c:∀ A:zx,zo (λ a b=>A b a)=zo A:=λ A=>by simp only[zs];ring
 let e:zx ≃ₗ[KD] zx:=LinearEquiv.ofInvolutive (LinearMap.pi λ a=>LinearMap.pi λ b=>(proj a:(Fin 3->KD) →ₗ[KD] KD) ∘ₗ proj b) λ _=>rfl;have⟨g,h⟩:=jH (λ a b=>B b a) (N.map (e:zx →ₗ[KD] zx)) (by rw[LinearEquiv.finrank_map_eq,h3]) (λ _ ⟨S,d,f⟩ b=>f ▸ h0 S d b) (by rwa[c]) λ _ ⟨S,d,f⟩=>f ▸ (c (B+S)).trans ((hN S d).trans (c B).symm);exact⟨g,λ n i j k=>(h n i j k).imp (N.mem_map_equiv).1 (N.mem_map_equiv).1⟩
lemma wD {E F:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] [AddCommGroup F] [Module KD F] (f:E →ₗ[KD] F) (K:Submodule KD E) (h:finrank KD (K.map f)<finrank KD K):∃ Y∈K,Y≠0/\f Y=0:=by
 have⟨Y,a,b⟩:=exists_mem_ne_zero_of_ne_bot (p:=K⊓LinearMap.ker f) λ e=>by have:=zW f K;rw[e,finrank_bot] at this;omega
 exact⟨Y,a.1,b,a.2⟩
lemma wE:∀ i p:Fin 3,p=i\/∃ a,p=z6 i a:=by decide
def w6 (T:ze) (r k:Fin 4) (z:KD):KD :=
 zo λ a b=>1+z*T (z8 r a,z8 k b)
lemma Qq (A:zx) (z:KD):zo (λ a b=>1+z*A a b)=6+z*qm (λ _ _=>1) A+z^2*qm A (λ _ _=>1)+z^3*zo A:=by have:=ji 1 z (λ _ _=>1) A;simp only[one_mul,mul_one,one_pow] at this;rw[this,show zo (λ _ _=>(1:KD))=6 by norm_num[zs]]
lemma Qr (A:zx) (h:∀ z,zo (λ a b=>1+z*A a b)=6):qm (λ _ _=>1) A=0/\qm A (λ _ _=>1)=0/\zo A=0:=(qE 0 (qm (λ _ _=>1) A) (qm A λ _ _=>1) (zo A) λ z=>by linear_combination h z-Qq A z).2
lemma Wr {s a b p:KD} {C:KD->KD} (g:∀ z,C z=6+z*a+z^2*b+z^3*p) (h:∀ z,(4+z*s)*C z=24) (z:KD):C z=6:=by
 obtain⟨-,c,d,e,f⟩:=qD 0 (4*a+6*s) (4*b+s*a) (4*p+s*b) (s*p) λ z=>by grind
 grind
lemma Ws (l:zg L) {r:Fin 4} (m:∀ w:Fin 4->KD,∑ j,w j=0->(λ p:Fin 4 × Fin 4=>if p.1=r then w p.2 else 0)∈L) {T:ze} (n:T∈L) (j:Fin 4) (z:KD):w6 T r j z=6:=by
 have g:∀ a,z8 r a≠r:=by fin_cases r<;>decide
 have b:∀ (z:KD) (w:Fin 4->KD),∑ k,w k=0->∑ k,(1+z*T (r,k)+w k)*w6 T r k z=24:=λ z w h=>by have:=l _ (L.add_mem (L.smul_mem z n) (m w h));rw[yd _ r] at this;simpa[w6,g,add_assoc] using this
 have i:∀ z,w6 T r 1 z=w6 T r 0 z/\w6 T r 2 z=w6 T r 0 z/\w6 T r 3 z=w6 T r 0 z/\(4+z*∑ k,T (r,k))*w6 T r 0 z=24:=λ z=>by have c:=b z 0 (by simp);have d:=b z ![-1,1,0,0] (by simp[sum_univ_four]);have e:=b z ![-1,0,1,0] (by simp[sum_univ_four]);have f:=b z ![-1,0,0,1] (by simp[sum_univ_four]);simp only[sum_univ_four] at c d e f⊢;simp at c d e f;grind
 have o:=Wr (C:=w6 T r 0) (λ z=>Qq _ z) (λ z=>(i z).2.2.2);fin_cases j<;>grind
abbrev Zo {ι:Type} (p q:ι->KD) (i j k:ι):Prop :=
 p i*(q j+q k)+p j*(q i+q k)+p k*(q i+q j)=0/\p i*p j*p k=q i*q j*q k
abbrev ka (p q:Fin 4->KD):Prop:=∀ i j k,i≠j -> i≠k -> j≠k -> Zo p q i j k
lemma Wt {z:KD} (f:z^2 = -3) {X:Fin 3 -> Fin 4->KD} (e:∀ m,X 2 m = -X 0 m-X 1 m) (l:Fin 4) (h:∀ w,zo (λ a b=>1+w*X a (z8 l b))=6):Zo (λ m=>2*X 0 m+(1-z)*X 1 m) (λ m=>2*X 0 m+(1+z)*X 1 m) (z8 l 0) (z8 l 1) (z8 l 2):=by obtain⟨-,c,d⟩:=Qr _ h;simp[qm,zK,zs,z6,sum_univ_three,e] at c d;grind
lemma Wu {p q:Fin 4->KD} (h:∀ l,Zo p q (z8 l 0) (z8 l 1) (z8 l 2)):ka p q:=by
 have a:=h 0;have b:=h 1;have c:=h 2;have d:=h 3;simp[z8] at a b c d;intro i j k e f g;fin_cases i<;>fin_cases j<;>fin_cases k<;>simp at e f g⊢ <;>
 first
 | exact⟨by linear_combination a.1,by linear_combination a.2⟩
 | exact⟨by linear_combination b.1,by linear_combination b.2⟩
 | exact⟨by linear_combination c.1,by linear_combination c.2⟩
 | exact⟨by linear_combination d.1,by linear_combination d.2⟩
lemma Qs {z:KD} (k:z^2 = -3) {X:Fin 3 -> Fin 4->KD} (h:∀ j w,zo (λ a b=>1+w*X a (z8 j b))=6):(∀ m,X 2 m = -X 0 m-X 1 m)/\ka (λ m=>2*X 0 m+(1-z)*X 1 m) (λ m=>2*X 0 m+(1+z)*X 1 m):=by
 have e:=λ j=>(Qr _ (h j)).1;have c:=e 0;have d:=e 1;have f:=e 2;have g:=e 3;simp[qm,zK,z8,sum_univ_three] at c d f g;have i:∀ m,X 2 m = -X 0 m-X 1 m:=by
  intro m;fin_cases m<;>simp only[zero_eta,mk_one,reduceFinMk]
  . linear_combination (c+d+f+g)/6-c/2
  . linear_combination (c+d+f+g)/6-d/2
  . linear_combination (c+d+f+g)/6-f/2
  grind
 exact⟨i,Wu λ l=>Wt k i l (h l)⟩
lemma Ww {p q:Fin 4->KD} (H:ka p q):ka q p:=λ i j k a b c=>⟨by linear_combination (H i j k a b c).1,(H i j k a b c).2.symm⟩
lemma Qt {p q:Fin 4->KD} (H:ka p q) {i j k l:Fin 4} (a:i≠j) (b:i≠k) (c:i≠l) (d:j≠k) (e:j≠l) (f:k≠l):p i*p j*p k=0:=by by_contra g;have⟨h,m⟩:=H i j k a b d;have⟨n,o⟩:=H i j l a c e;have⟨r,s⟩:=H i k l b c f;have⟨t,u⟩:=H j k l d e f;grind
lemma Wx {p q:Fin 4->KD} (H:ka p q) {i j k l:Fin 4} (a:i≠j) (b:i≠k) (c:i≠l) (d:j≠k) (e:j≠l) (f:k≠l) (g:p k=0) (h:p l=0) (m:p i≠0):q k=0/\q l=0\/q i=0/\q j=0:=by grind
lemma Wy:∀ m:Fin 4,m≠z8 m 0/\m≠z8 m 1/\m≠z8 m 2/\z8 m 0≠z8 m 1/\z8 m 0≠z8 m 2/\z8 m 1≠z8 m 2:=by decide
lemma Qu {f:Fin 4->KD} (p:∀ i j k l:Fin 4,i≠j -> i≠k -> i≠l -> j≠k -> j≠l -> k≠l -> f i*f j*f k=0) (m:Fin 4) (q:f m≠0):∃ j k l,m≠j/\m≠k/\m≠l/\j≠k/\j≠l/\k≠l/\f k=0/\f l=0:=by
 have⟨d1,d2,d3,d4,d5,d6⟩:=Wy m;generalize z8 m 0=a at *;generalize z8 m 1=b at *;generalize z8 m 2=c at *;have g:=p m a b c d1 d2 d3 d4 d5 d6;have h:=p m a c b d1 d3 d2 d5 d4 d6.symm;have n:=p m b c a d2 d3 d1 d6 d4.symm d5.symm;simp[q] at g h n;rcases g with d|e
 . rcases n with e|o
   . exact⟨c,a,b,d3,d1,d2,d5.symm,d6.symm,d4,d,e⟩
   . exact⟨b,a,c,d2,d1,d3,d4.symm,d6,d5,d,o⟩
 . rcases h with d|o
   . exact⟨c,a,b,d3,d1,d2,d5.symm,d6.symm,d4,d,e⟩
   . exact⟨a,b,c,d1,d2,d3,d4,d5,d6,e,o⟩
lemma WA {p q:Fin 4->KD} (H:ka p q):∃ i j k l:Fin 4,i≠j/\i≠k/\i≠l/\j≠k/\j≠l/\k≠l/\p k=0/\p l=0/\(q k=0/\q l=0\/q i=0/\q j=0):=by
 by_cases a:∃ m,p m≠0
 . have⟨m,b⟩:=a;have⟨j,k,l,c,d,e,f,g,h,n,o⟩:=Qu (λ _ _ _ _=>Qt H) m b;exact⟨m,j,k,l,c,d,e,f,g,h,n,o,Wx H c d e f g h n o b⟩
 push Not at a;by_cases r:∃ m,q m≠0
 . have⟨m,b⟩:=r;have⟨j,k,l,c,d,e,f,g,h,n,o⟩:=Qu (λ _ _ _ _=>Qt (Ww H)) m b;exact⟨m,j,k,l,c,d,e,f,g,h,a k,a l,Or.inl ⟨n,o⟩⟩
 push Not at r;exact⟨0,1,2,3,by decide,by decide,by decide,by decide,by decide,by decide,a 2,a 3,Or.inl ⟨r 2,r 3⟩⟩
open LinearMap in
lemma Qv {E:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] (N:Submodule KD E) (f g h k:E →ₗ[KD] KD) (H:∀ x∈N,f x*k x+g x*h x=0) (I:∀ x∈N,f x=0 -> g x=0 -> h x=0 -> k x=0 -> x=0):finrank KD N≤2:=by
 let Ψ:E →ₗ[KD] Fin 4->KD:=LinearMap.pi ![f,g,h,k];let B:(Fin 4->KD) →ₗ[KD] (Fin 4->KD) →ₗ[KD] KD:=mk₂ KD (λ v w=>v 0*w 3+v 3*w 0+v 1*w 2+v 2*w 1) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring);have e:=zW Ψ N;have i:N⊓ker Ψ=⊥:=eq_bot_iff.2 λ x ⟨c,j⟩=>by have:=mem_ker.1 j;exact(mem_bot KD).2 (I x c (congrFun this 0) (congrFun this 1) (congrFun this 2) (congrFun this 3))
 have l:=Kk B (N.map Ψ) (N.map Ψ) ?_ (λ a=>Pi.single a 1) (λ b=>Pi.single (![3,2,1,0] b) 1) ?_
 . rw[i,finrank_bot] at e;rw[finrank_fin_fun] at l;omega
 . rintro _ ⟨x,c,rfl⟩ _ ⟨y,d,rfl⟩;have:=H _ (N.add_mem c d);simp[B,Ψ] at this⊢;linear_combination this-H x c-H y d
 . intro a b;fin_cases a<;>fin_cases b<;>simp[B]
lemma kb {E:Type} [AddCommGroup E] [Module KD E] {ι:Type} [Fintype ι] (N:Submodule KD E) (F:ι -> E →ₗ[KD] KD):∃ x∈N,∀ i,F i x=0->∀ y∈N,F i y=0:=by
 classical
 suffices ∀ s:Finset ι,∃ x∈N,∀ i∈s,F i x=0->∀ y∈N,F i y=0 by have⟨x,a,h⟩:=this univ;exact⟨x,a,λ i=>h i (mem_univ i)⟩
 intro s;induction s using Finset.induction_on with
 | empty=>exact⟨0,N.zero_mem,by simp⟩
 | insert j s _ ih =>
  have⟨x,a,h⟩:=ih
  by_cases b:∀ y∈N,F j y=0
  . exact⟨x,a,λ i c=>(mem_insert.1 c).elim (λ e=>e ▸ λ _=>b) (h i)⟩
  push Not at b
  have⟨y,d,g⟩:=b
  have⟨t,k⟩:=Infinite.exists_notMem_finset ((insert j s).image λ i=>-F i x/F i y)
  refine⟨x+t•y,N.add_mem a (N.smul_mem t d),λ i c f=>?_⟩
  simp only[map_add,map_smul,smul_eq_mul] at f
  grind
lemma j4:∀ r i:Fin 4,i≠r->∃ a,z8 r a=i:=by decide
def Qw (c:KD) (m:Fin 4):(Fin 3 -> Fin 4->KD) →ₗ[KD] KD where
 toFun X:=2*X 0 m+c*X 1 m
 map_add' _ _:=by simp only[Pi.add_apply];ring
 map_smul' _ _:=by simp only[Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring
lemma WB:∀ i j k l m:Fin 4,i≠j -> i≠k -> i≠l -> j≠k -> j≠l -> k≠l -> m=i\/m=j\/m=k\/m=l:=by decide
lemma WC {z:KD} (C:z^2 = -3) (N:Submodule KD (Fin 3 -> Fin 4->KD)) (D:∀ X∈N,∀ j w,zo (λ a b=>1+w*X a (z8 j b))=6):finrank KD N≤2:=by
 let a:=Qw (1-z);let b:=Qw (1+z);have Q:∀ y∈N,ka (λ m=>a m y) (λ m=>b m y):=λ y c=>(Qs C (D y c)).2;have R:z≠0:=by grind
 have o:∀ X∈N,(∀ m,a m X=0)->(∀ m,b m X=0) -> X=0:=λ X E F G=>by
  funext u m;have S:2*X 0 m+(1-z)*X 1 m=0:=F m;have T:2*X 0 m+(1+z)*X 1 m=0:=G m;have H:X 1 m=0:=by grind
  have I:X 0 m=0:=by grind
  fin_cases u<;>simp[(Qs C (D X E)).1,I,H]
 have⟨x,J,p⟩:=kb N (Sum.elim a b);have⟨i,j,k,l,q,r,K,s,L,M,t,O,h⟩:=WA (Q x J);have e:∀ m,a m x=0->∀ y∈N,a m y=0:=λ m=>p (Sum.inl m);have f:∀ m,b m x=0->∀ y∈N,b m y=0:=λ m=>p (Sum.inr m);have d:=λ m=>WB i j k l m q r K s L M;rcases h with⟨v,P⟩|⟨U,V⟩
 . refine Qv N (a i) (a j) (b i) (b j) (λ y c=>?_) λ y c g A n B=>o y c (λ m=>?_) λ m=>?_
   . linear_combination (Q y c i j k q r s).1-(a i y+a j y)*f k v y c-(b i y+b j y)*e k t y c
   . rcases d m with rfl|rfl|rfl|rfl
     exacts[g,A,e _ t y c,e _ O y c]
   . rcases d m with rfl|rfl|rfl|rfl
     exacts[n,B,f _ v y c,f _ P y c]
 . refine Qv N (a i+a j) (a i) (b k+b l) (b k) (λ y c=>?_) λ y c g A n B=>?_
   . simp only[LinearMap.add_apply];grind
   . simp only[LinearMap.add_apply] at g n;refine o y c (λ m=>?_) λ m=>?_<;>rcases d m with rfl|rfl|rfl|rfl<;>grind
open LinearMap in
lemma wL (hL:zg L) (r:Fin 4) (hU:∀ w:Fin 4->KD,∑ j,w j=0->(λ p:Fin 4 × Fin 4=>if p.1=r then w p.2 else 0)∈L):finrank KD L≤5:=by
 have c:(Real.sqrt 3*Complex.I)^2 = -3:=by rw[mul_pow,Complex.I_sq,←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)];norm_num
 let D:ze →ₗ[KD] Fin 3 -> Fin 4->KD:=LinearMap.pi λ a=>LinearMap.pi λ m=>proj (z8 r a,m);have l:=WC c (L.map D) (by rintro _ ⟨T,d,rfl⟩ j w;exact Ws hL hU d j w);have n:=zW D L;have e:=zW (z9 r) (L⊓ker D);have o:=(finrank_mono (map_mono (f:=z9 r) (inf_le_left:L⊓ker D≤L))).trans (yq hL r);have g:L⊓ker D⊓ker (z9 r)=⊥:=eq_bot_iff.2 λ T ⟨⟨_,h⟩,k⟩=>(mem_bot KD).2 (funext λ ⟨i,j⟩=>by
  by_cases b:i=r
  . subst b;exact congrFun (mem_ker.1 k) j
  . obtain⟨a,rfl⟩:=j4 r i b;exact congrFun (congrFun (mem_ker.1 h) a) j)
 rw[g,finrank_bot] at e;omega
def ys (x y w:Fin 4->KD):KD :=
 x 0*(w 1*(y 2*y 3)+w 2*(y 1*y 3)+w 3*(y 1*y 2)) +
 x 1*(w 0*(y 2*y 3)+w 2*(y 0*y 3)+w 3*(y 0*y 2)) +
 x 2*(w 0*(y 1*y 3)+w 1*(y 0*y 3)+w 3*(y 0*y 1)) +
 x 3*(w 0*(y 1*y 2)+w 1*(y 0*y 2)+w 2*(y 0*y 1))
def y6 (r:Fin 4) (w:Fin 4->KD):ze:=λ p=>if p.1=r then w p.2 else 0
lemma Zq (X:Fin 4 -> Fin 4->KD) (h:∀ j,X 2 j=X 1 j):ql X=2*ys (X 0) (X 1) (X 3):=by rw[zY];simp[zs,ys,h];ring
lemma Zr (e:zg L) (a:∀ T∈L,∀ j,T (1,j)=T (2,j)) {T Y:ze} (b:T∈L) (c:Y∈L) (d:∀ j,Y (1,j)=0) (s:KD):ys (λ j=>Y (0,j)) (λ j=>s+T (1,j)) (λ j=>Y (3,j))=0/\ys (λ j=>Y (0,j)) (λ j=>s+T (1,j)) (λ j=>s+T (3,j))+ys (λ j=>s+T (0,j)) (λ j=>s+T (1,j)) (λ j=>Y (3,j))=0:=by
 have h:=λ z:KD=>(Zq _ λ j=>by simp[a T b j,a Y c j]).symm.trans (qP e (L.add_mem b (L.smul_mem z c)) s);obtain⟨-,f,g⟩:=qc (2*ys (λ j=>s+T (0,j)) (λ j=>s+T (1,j)) (λ j=>s+T (3,j))-24*s^4) (2*(ys (λ j=>Y (0,j)) (λ j=>s+T (1,j)) (λ j=>s+T (3,j))+ys (λ j=>s+T (0,j)) (λ j=>s+T (1,j)) (λ j=>Y (3,j)))) (2*ys (λ j=>Y (0,j)) (λ j=>s+T (1,j)) (λ j=>Y (3,j))) λ z=>by have:=h z;simp only[ys,Pi.add_apply,Pi.smul_apply,smul_eq_mul,d,mul_zero,add_zero] at this⊢;linear_combination this
 grind
lemma x7 (b:zg L) (e:∀ T∈L,∀ j,T (1,j)=T (2,j)):finrank KD (L.map (z9 1))≤2:=by
 by_contra n;obtain⟨g,-⟩:=qu b (le_antisymm (yq b 1) (by omega));apply qg b 1;have c:∀ k:Fin 4,(λ j=>if j=k then (1:KD) else 0)∈L.map (z9 1):=λ k=>by
  have⟨a,T,d,c⟩:=g λ j=>if j=k then 1 else 0
  have f:∀ j,a+T (1,j)=if j=k then 1 else 0:=λ j=>(congrFun c j).symm
  have h:=(Zq (λ i j=>a+T (i,j)) λ j=>by simp[e T d j]).symm.trans (qP b d a);have l:ys (λ j=>a+T (0,j)) (λ j=>a+T (1,j)) (λ j=>a+T (3,j))=0:=by rw[show(λ j=>a+T (1,j))=λ j=>if j=k then 1 else 0 from funext f];fin_cases k<;>simp[ys]
  rw[l,mul_zero] at h;have m:a=0:=by grind
  exact⟨T,d,funext λ j=>by rw[zA,←f j,m,zero_add]⟩
 rw[show(λ _=>(1:KD))=∑ k:Fin 4,λ j=>if j=k then (1:KD) else 0 by funext j;simp[Finset.sum_apply]];exact Submodule.sum_mem _ λ k _=>c k
open LinearMap in
lemma WD {E:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] (K:Submodule KD E) (f g:E →ₗ[KD] KD) (h:∀ x∈K,f x=0 -> g x=0 -> x=0):finrank KD K≤2:=by
 have b:=zW (LinearMap.prod f g) K;have c:K⊓ker (LinearMap.prod f g)=⊥:=eq_bot_iff.2 λ x ⟨d,a⟩=>by exact(mem_bot KD).2 (h x d (congrArg Prod.fst (mem_ker.1 a)) (congrArg Prod.snd (mem_ker.1 a)))
 have e:=finrank_le (K.map (LinearMap.prod f g));rw[c,finrank_bot] at b;simp at e;omega
lemma Zs {E F:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] [AddCommGroup F] [Module KD F] (K:Submodule KD E) (φ:E →ₗ[KD] F) (h:∀ x∈K,φ x=0 -> x=0):finrank KD (K.map φ)=finrank KD K:=by have a:=zW φ K;have b:K⊓LinearMap.ker φ=⊥:=eq_bot_iff.2 λ x ⟨c,d⟩=>(mem_bot KD).2 (h x c d);rw[b,finrank_bot] at a;omega
open LinearMap in
lemma Qx {n:ℕ} (g:(n:KD)*(n-1)≠0) (U:Submodule KD ((Fin n->KD) × (Fin n->KD))) (h:∀ x∈U,dotProduct x.1 1*dotProduct 1 x.2-dotProduct x.1 x.2=0/\dotProduct x.1 1+dotProduct 1 x.2=0):2*finrank KD U+1≤2*n:=by
 have u:(n:KD)≠0:=left_ne_zero_of_mul g;have i:(n:KD)-1≠0:=right_ne_zero_of_mul g;let B:((Fin n->KD) × (Fin n->KD)) →ₗ[KD] ((Fin n->KD) × (Fin n->KD)) →ₗ[KD] KD :=
  mk₂ KD (λ x y=>dotProduct x.1 1*dotProduct 1 y.2+dotProduct y.1 1 *
   dotProduct 1 x.2-dotProduct x.1 y.2-dotProduct y.1 x.2)
   (by intros;simp[add_dotProduct,dotProduct_add];ring)
   (by intros;simp[smul_dotProduct,dotProduct_smul];ring)
   (by intros;simp[add_dotProduct,dotProduct_add];ring)
   (by intros;simp[smul_dotProduct,dotProduct_smul];ring)
 have c:∀ x y,B x y=dotProduct x.1 1*dotProduct 1 y.2+dotProduct y.1 1 *
  dotProduct 1 x.2-dotProduct x.1 y.2-dotProduct y.1 x.2:=λ _ _=>rfl
 have f:ker B=⊥:=eq_bot_iff.2 λ x a=>by
  have d:∀ y,B x y=0:=λ y=>by rw[mem_ker.1 a];rfl
  have j:∀ k,x.1 k=dotProduct x.1 1:=λ k=>by have:=d (0,Pi.single k 1);simp[c] at this;linear_combination -this
  have l:∀ k,x.2 k=dotProduct 1 x.2:=λ k=>by have:=d (Pi.single k 1,0);simp[c] at this;linear_combination -this
  have q:dotProduct x.1 1=0:=by
   have:dotProduct x.1 1=n*dotProduct x.1 1:=by
    conv_lhs=>rw[dotProduct];simp only[Pi.one_apply,mul_one];rw[sum_congr rfl λ k _=>j k]
    simp
   grind
  have r:dotProduct 1 x.2=0:=by
   have:dotProduct 1 x.2=n*dotProduct 1 x.2:=by
    conv_lhs=>rw[dotProduct];simp only[Pi.one_apply,one_mul];rw[sum_congr rfl λ k _=>l k]
    simp
   grind
  exact(mem_bot KD).2 (Prod.ext (funext λ k=>by simp[j k,q])
   (funext λ k=>by simp[l k,r]))
 have e:dotProduct (1:Fin n->KD) 1=n:=by simp[dotProduct]
 have m:B ((n-1:KD)⁻¹•1,(n-1:KD)⁻¹•1) ((n-1:KD)⁻¹•1,(n-1:KD)⁻¹•1) =
  2*((n-1:KD)⁻¹)^2*(n*(n-1)):=by
  rw[c];simp only[dotProduct_smul,smul_dotProduct,smul_eq_mul,e];ring
 have:=Wo B U (b:=((n-1:KD)⁻¹•1,(n-1:KD)⁻¹•1))
  (λ x a y o=>by have p:=h _ (U.add_mem a o);have s:=h x a;have t:=h y o;simp only[Prod.fst_add,Prod.snd_add,add_dotProduct,dotProduct_add] at p;rw[c];linear_combination p.1-s.1-t.1)
  (λ x a=>by rw[c];simp only[dotProduct_smul,smul_dotProduct,smul_eq_mul,e];linear_combination (n-1:KD)⁻¹*(n-1)*(h x a).2)
  (by rw[m];exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (inv_ne_zero i))) g)
 rw[f,inf_bot_eq,finrank_bot,finrank_prod,finrank_fin_fun] at this;omega
open LinearMap in
lemma jP (a:∀ T∈L,∀ j,T (1,j)=T (2,j)) {T:ze} (h:T∈L⊓ker (z9 1)):T∈L/\∀ j,T (1,j)=0/\T (2,j)=0:=⟨h.1,λ j=>⟨congrFun (mem_ker.1 h.2) j,(a T h.1 j).symm.trans (congrFun (mem_ker.1 h.2) j)⟩⟩
lemma Zt (c:zg L) {T:ze} (d:T∈L) (h:∀ j,T (1,j)=0/\T (2,j)=0):(∑ j,T (0,j))*(∑ j,T (3,j))-∑ j,T (0,j)*T (3,j)=0/\∑ j,T (0,j)+∑ j,T (3,j)=0:=by obtain⟨a,b,-⟩:=qb c d;simp only[qY,yl,Fintype.sum_prod_type,sum_univ_four,(h _).1,(h _).2] at a b⊢;grind
lemma WE (p:Fin 4) (f:Fin 4->KD):∑ j,f j=f p+∑ b,f (z8 p b):=by fin_cases p<;>simp[sum_univ_four,sum_univ_three,z8]<;>ring
lemma WF:∀ p j:Fin 4,j=p\/∃ b,z8 p b=j:=by decide
lemma jp:∀ p b,z8 p b≠p:=by decide
open LinearMap in
lemma Qy (r:zg L) (c:∀ T∈L,∀ j,T (1,j)=T (2,j)) {n:ℕ} (s:(n:KD)*(n-1)≠0) (e:Fin n -> Fin 4) (K:Submodule KD ze) (p:K≤L⊓ker (z9 1)) (t:∀ T∈K,∀ j,(∀ b,e b≠j) -> T (0,j)=0/\T (3,j)=0) (d:∀ f:Fin 4->KD,(∀ j,(∀ b,e b≠j) -> f j=0)->∑ j,f j=∑ b,f (e b)):2*finrank KD K+1≤2*n:=by
 let π:ze →ₗ[KD] (Fin n->KD) × (Fin n->KD):=LinearMap.prod (funLeft KD KD e ∘ₗ z9 0) (funLeft KD KD e ∘ₗ z9 3);have q:=Zs K π λ T g k=>by
  obtain⟨-,h⟩:=jP c (p g);funext ⟨i,j⟩;have u:∀ b,T (0,e b)=0/\T (3,e b)=0:=λ b=>⟨congrFun (congrArg Prod.fst k) b,congrFun (congrArg Prod.snd k) b⟩;have a:T (0,j)=0/\T (3,j)=0:=by grind
  fin_cases i<;>simp_all
 rw[←q];refine Qx s _ ?_;rintro _ ⟨T,g,rfl⟩;have⟨l,h⟩:=jP c (p g);have⟨m,o⟩:=Zt r l h;have z:=t T g;rw[d _ λ j a=>(z j a).1,d _ λ j a=>(z j a).2,d _ λ j a=>by rw[(z j a).1,zero_mul]] at m;rw[d _ λ j a=>(z j a).1,d _ λ j a=>(z j a).2] at o;simp only[π,LinearMap.prod_apply,coe_comp,dotProduct,Pi.one_apply,mul_one,one_mul];exact⟨m,o⟩
lemma Zu (b:zg L) (a:∀ T∈L,∀ j,T (1,j)=T (2,j)):finrank KD (L⊓LinearMap.ker (z9 1):Submodule KD ze)≤3:=by have:=Qy b a (n:=4) (by norm_num) id _ le_rfl (λ _ _ j h=>absurd rfl (h j)) λ f _=>rfl;omega
open LinearMap in
lemma WG (i:zg L) (a:∀ T∈L,∀ j,T (1,j)=T (2,j)) (p:Fin 4) (k:∀ T∈L⊓ker (z9 1),T (0,p)=0/\T (3,p)=0):finrank KD (L⊓ker (z9 1):Submodule KD ze)≤2:=by
 have c:∀ j,(∀ b,z8 p b≠j) -> j=p:=λ j h=>(WF p j).resolve_right λ ⟨b,d⟩=>h b d;have:=Qy i a (n:=3) (by norm_num) (z8 p) _ le_rfl (λ T e j h=>c j h ▸ k T e) λ f g=>by rw[WE p f,g p (jp p),zero_add]
 omega
def x8 (r:Fin 4):(Fin 4->KD) →ₗ[KD] ze where
 toFun:=y6 r
 map_add' x y:=by funext p;simp only[y6,Pi.add_apply];split_ifs<;>simp
 map_smul' c x:=by funext p;simp only[y6,Pi.smul_apply,smul_eq_mul,
  RingHom.id_apply];split_ifs<;>simp
open LinearMap in
lemma Qz (k:zg L) {K:Submodule KD ze} (a:K≤L) (n:3≤finrank KD K) (r:Fin 4) (l:∀ T∈K,∀ i j,i≠r -> T (i,j)=0):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=by
 let σ:(Fin 4->KD) →ₗ[KD] KD:=∑ j,proj j;have b:∀ w,σ w=∑ j,w j:=λ w=>by simp[σ]
 have m:finrank KD ((ker σ).map (x8 r))≤3:=(finrank_map_le _ _).trans (wK _ λ h=>by rw[mem_ker,b] at h;simp at h);have c:K≤(ker σ).map (x8 r):=λ T d=>by
  have:=(qb k (a d)).1;simp only[qY,Fintype.sum_prod_type] at this;rw[sum_eq_single r (λ i _ f=>sum_eq_zero λ j _=>l T d i j f) (by simp)] at this;refine⟨λ j=>T (r,j),mem_ker.2 (by rw[b];exact this),funext λ ⟨i,j⟩=>?_⟩;show y6 r (λ j=>T (r,j)) (i,j)=T (i,j);simp only[y6];split_ifs with h
  . rw[h]
  grind
 have e:=eq_of_le_of_finrank_le c (by omega);exact⟨r,λ w g=>a (e ▸ ⟨w,mem_ker.2 (by rw[b];exact g),rfl⟩)⟩
def zf (p:Fin 4 × Fin 4):ze →ₗ[KD] KD:=LinearMap.proj p
lemma QA (s:Fin 4) {b d:ze} (e:b∈L) (q:d∈L) (r:∀ k,b (1,k)=if k=2 then 1 else 0) (u:∀ k,d (1,k)=if k=3 then 1 else 0) (c:∀ T∈L,T (1,0)=0/\T (1,1)=0) (f:∀ T∈L,∀ t:KD,ys ![0,0,1,-1] (λ k=>t+T (1,k)) (λ k=>t+T (s,k))=0/\ys ![1,1,0,-2] (λ k=>t+T (1,k)) (λ k=>t+T (s,k))=0):False:=by
 have R:∀ T∈L,(T (1,3)-T (1,2))*(T (s,0)+T (s,1))=0/\2*(T (1,3)-T (1,2))+T (s,3)-T (s,2)=0/\(T (1,3)-T (1,2))*(T (s,0)+T (s,1))+2*T (1,2)*T (1,3)+2*T (1,3)*T (s,2)+2*T (1,2)*T (s,3)=0/\-(T (s,0)+T (s,1))+4*T (1,3)+2*T (s,3)=0:=λ T a=>by
  obtain⟨-,g,i⟩:=qc 0 ((T (1,3)-T (1,2))*(T (s,0)+T (s,1))) (2*(T (1,3)-T (1,2))+T (s,3)-T (s,2)) λ t=>by have:=(f T a t).1;simp only[ys,Matrix.cons_val,(c T a).1,(c T a).2] at this;linear_combination this
  obtain⟨-,j,l⟩:=qc (T (1,2)*T (1,3)*(T (s,0)+T (s,1))) ((T (1,3)-T (1,2))*(T (s,0)+T (s,1))+2*T (1,2)*T (1,3)+2*T (1,3)*T (s,2)+2*T (1,2)*T (s,3)) (-(T (s,0)+T (s,1))+4*T (1,3)+2*T (s,3)) λ t=>by have:=(f T a t).2;simp only[ys,Matrix.cons_val,(c T a).1,(c T a).2] at this;linear_combination this
  exact⟨g,i,j,l⟩
 have m:=(zz L (zf (1,3)-zf (1,2)) (zf (s,0)+zf (s,1)) λ T a=>(R T a).1).resolve_left λ h=>by have:b (1,3)-b (1,2)=0:=h b e;grind
 have a:=L.add_mem e q;obtain⟨-,n,o,p⟩:=R _ a;have v:b (s,0)+d (s,0)+(b (s,1)+d (s,1))=0:=m _ a;simp only[Pi.add_apply,r,u] at n o p;grind
lemma QB {E:Type} [AddCommGroup E] [Module KD E] (K:Submodule KD E) (f g:E →ₗ[KD] KD) {a b:E} (c:a∈K) (d:b∈K) (e:f a*g b-f b*g a≠0):∃ e1∈K,∃ e2∈K,f e1=1/\g e1=0/\f e2=0/\g e2=1:=⟨(f a*g b-f b*g a)⁻¹•(g b•a-g a•b),K.smul_mem _ (K.sub_mem (K.smul_mem _ c) (K.smul_mem _ d)),(f a*g b-f b*g a)⁻¹•(f a•b-f b•a),K.smul_mem _ (K.sub_mem (K.smul_mem _ d) (K.smul_mem _ c)),by simp only[map_smul,map_sub,smul_eq_mul];field_simp,by simp only[map_smul,map_sub,smul_eq_mul];ring,by simp only[map_smul,map_sub,smul_eq_mul];ring,by simp only[map_smul,map_sub,smul_eq_mul];field_simp⟩
lemma Zw (a:∀ T∈L,∀ j,T (1,j)=T (2,j)) {Y:ze} (b:Y∈L⊓LinearMap.ker (z9 1)) (h:∀ j,Y (0,j)=0/\Y (3,j)=0):Y=0:=funext λ ⟨i,j⟩=>by obtain⟨-,c⟩:=jP a b;fin_cases i<;>simp_all
open LinearMap in
lemma WH (o:zg L) (h5:finrank KD L=5) (d:∀ T∈L,∀ j,T (1,j)=T (2,j)) (μ:Fin 4->KD) (a3:μ 0≠0) (a4:μ 1≠0) (a5:μ 2≠0) (hQ:∀ y:Fin 4->KD,∑ k,μ k*y k=0->∃ s:KD,∃ T∈L,y=λ k=>s+T (1,k)):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=by
 have N:finrank KD (L⊓ker (z9 1):Submodule KD ze)=3:=by have:=zW (z9 1) L;have:=x7 o d;have:=Zu o d;omega
 set K:=L⊓ker (z9 1) with O
 have C:∀ Y∈K,∀ y:Fin 4->KD,∑ k,μ k*y k=0 -> ys (λ j=>Y (0,j)) y (λ j=>Y (3,j))=0:=λ Y c y hy=>by obtain⟨s,T,g,rfl⟩:=hQ y hy;have⟨p,e⟩:=jP d c;exact(Zr o d g p (λ j=>(e j).1) s).1
 have g3:∀ Y∈K,Y (0,3)*Y (3,0)+Y (3,3)*Y (0,0)=0/\Y (0,3)*Y (3,1)+Y (3,3)*Y (0,1)=0/\Y (0,3)*Y (3,2)+Y (3,3)*Y (0,2)=0:=λ Y c=>by have D:=C Y c ![0,μ 2,-μ 1,0] (by simp[sum_univ_four];ring);have E:=C Y c ![μ 2,0,-μ 0,0] (by simp[sum_univ_four];ring);have F:=C Y c ![μ 1,-μ 0,0,0] (by simp[sum_univ_four];ring);simp only[ys,Matrix.cons_val] at D E F;grind
 have t:∀ Y∈K,∀ j:Fin 4,j≠3 -> Y (0,3)*Y (3,j)+Y (3,3)*Y (0,j)=0:=λ Y c j l=>by grind
 have u:∀ r s:Fin 4,(∀ Y∈K,∀ j,Y (s,j)=0) -> r=0/\s=3\/r=3/\s=0->∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=λ r s P hr=>Qz o inf_le_left N.ge r λ T g i j Q=>by
  obtain⟨-,e⟩:=jP d g;rcases hr with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>fin_cases i<;>simp at Q⊢
  exacts[(e j).1,(e j).2,P T g j,P T g j,(e j).1,(e j).2]
 by_cases v:∃ G∈K,∃ H∈K,G (0,3)*H (3,3)-H (0,3)*G (3,3)≠0
 . exfalso
   have⟨G,E,H,F,hD⟩:=v;have⟨R,S,U,V,f1,f2,f3,f4⟩:=QB K (zf (0,3)) (zf (3,3)) E F hD;have I:=λ j l=>yF K (zf (0,3)) (zf (3,3)) (zf (0,j)) (zf (3,j)) S V f1 f2 f3 f4 λ Y c=>t Y c j l;have⟨k0,W⟩:=I 0 (by decide);have⟨k1,X⟩:=I 1 (by decide);have⟨k2,Z⟩:=I 2 (by decide);have:=WD K (zf (0,3)) (zf (3,3)) λ Y c m z=>Zw d c λ j=>by have e0:=W Y c;have R:=X Y c;have U:=Z Y c;simp only[zf,proj_apply] at m z e0 R U;grind
   omega
 push Not at v;by_cases m:∃ f∈K,f (0,3)≠0
 . have⟨f,A,a1⟩:=m
   have B:∀ Y∈K,Y (3,3)=f (3,3)/f (0,3)*Y (0,3):=by grind
   set κ:=f (3,3)/f (0,3);have J:∀ j:Fin 4,j≠3->∀ Y∈K,Y (3,j)+κ*Y (0,j)=0:=λ j l=>(zz K (zf (0,3)) (zf (3,j)+κ•zf (0,j)) λ Y c=>by have:=t Y c j l;rw[B Y c] at this;simp only[LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,zf,proj_apply];linear_combination this).resolve_left λ h=>a1 (h f A);by_cases hκ:κ=0
   . refine u 0 3 (λ Y c j=>?_) (Or.inl ⟨rfl,rfl⟩);grind
   exfalso;let n:(Fin 4->KD) →ₗ[KD] (Fin 4->KD) →ₗ[KD] KD:=mk₂ KD (λ a b=>(a 0+a 1+a 2)*(b 0+b 1+b 2)-(a 0*b 0+a 1*b 1+a 2*b 2)) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring);have Q:=Zs K (z9 0) λ Y c D=>Zw d c λ j=>by have a0:∀ k,Y (0,k)=0:=λ k=>congrFun D k;grind
   have M:∀ x∈K.map (z9 0),n x x=0:=by
    rintro _ ⟨Y,c,rfl⟩;have⟨p,e⟩:=jP d c;have q:=(Zt o p e).1;simp only[sum_univ_four] at q;have E0:=J 0 (by decide) Y c;have E1:=J 1 (by decide) Y c;have E2:=J 2 (by decide) Y c;have E3:=B Y c;have:κ*((Y (0,0)+Y (0,1)+Y (0,2))*(Y (0,0)+Y (0,1)+Y (0,2))-(Y (0,0)*Y (0,0)+Y (0,1)*Y (0,1)+Y (0,2)*Y (0,2)))=0:=by grind
    simpa[n,zA,hκ] using this
   have:=Kk n _ _ (yr n (λ x y=>by simp[n];ring) _ M) ![![1,0,0,0],![0,1,0,0],![0,0,1,0]] ![![-1/2,1/2,1/2,0],![1/2,-1/2,1/2,0],![1/2,1/2,-1/2,0]] (by intro a b;fin_cases a<;>fin_cases b<;>simp[n]<;>norm_num);rw[finrank_fin_fun] at this;omega
 push Not at m;by_cases z:∃ f∈K,f (3,3)≠0
 . have⟨f,A,a2⟩:=z
   refine u 3 0 (λ Y c j=>?_) (Or.inr ⟨rfl,rfl⟩);by_cases l:j=3
   . subst l;exact m Y c
   . exact(zz K (zf (3,3)) (zf (0,j)) (λ Y c=>by
      have:=t Y c j l;rw[m Y c,zero_mul,zero_add] at this;exact this)).resolve_left
      (λ h=>a2 (h f A)) Y c
 push Not at z;have:=WG o d 3 λ T g=>⟨m T g,z T g⟩;rw[←O] at this;omega
lemma QC {E:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] (K:Submodule KD E) (f:E →ₗ[KD] KD) (h:∀ x∈K,f x=0 -> x=0):finrank KD K≤1:=by rw[←Zs K f h];exact(finrank_le _).trans (by simp)
open LinearMap in
lemma QD {E F G:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] [AddCommGroup F] [Module KD F] [AddCommGroup G] [Module KD G] (K:Submodule KD E) (Γ:E →ₗ[KD] F) (ψ:E →ₗ[KD] G) (h:∀ Y∈K,ψ Y=0->Γ Y=0):finrank KD (K.map Γ)≤finrank KD (K.map ψ):=by have:=zW Γ K;have:=zW ψ K;have:=finrank_mono (show K⊓ker ψ≤K⊓ker Γ from λ Y ⟨a,b⟩=>⟨a,h Y a b⟩);omega
lemma QE {K:Submodule KD ze} (o:3≤finrank KD K) {r s:Fin 4} (f:r≠s) (p:∀ Y∈K,(∀ i j,i≠r -> i≠s -> Y (i,j)=0)/\Y (r,1)=Y (r,0)/\Y (r,3) = -2*Y (r,0)-Y (r,2)/\Y (s,1) = -Y (s,0)/\Y (s,2)=0/\Y (s,3)=0):y6 r ![0,0,1,-1]∈K/\y6 r ![1,1,0,-2]∈K:=by
 let M:(Fin 3->KD) →ₗ[KD] ze:=x8 r ∘ₗ mulVecLin !![1,0,0;1,0,0;0,1,0;-2,-1,0]+x8 s ∘ₗ mulVecLin !![0,0,1;0,0,-1;0,0,0;0,0,0];have a:∀ q i j,M q (i,j)=(if i=r then ![q 0,q 0,q 1,-2*q 0-q 1] j else 0)+(if i=s then ![q 2,-q 2,0,0] j else 0):=λ q i j=>by simp only[M,LinearMap.add_apply,LinearMap.comp_apply,Pi.add_apply];change y6 r _ (i,j)+y6 s _ (i,j)=_;simp only[y6];congr 1<;>split_ifs<;>fin_cases j<;>simp[mulVec,dotProduct,sum_univ_three];ring
 have b:K≤LinearMap.range M:=λ Y g=>by
  have⟨t,h,k,l,m,n⟩:=p Y g;refine⟨![Y (r,0),Y (r,2),Y (s,0)],funext λ ⟨i,j⟩=>?_⟩;rw[a];by_cases c:i=r
  . subst c;fin_cases j<;>simp[f,h,k]
  by_cases d:i=s
  . subst d;fin_cases j<;>simp[c,l,m,n]
  grind
 have e:=eq_of_le_of_finrank_le b (o.trans' ((LinearMap.finrank_range_le M).trans (by simp)));rw[e];exact⟨⟨![0,1,0],funext λ ⟨i,j⟩=>by
  rw[a];simp only[y6];split_ifs<;>fin_cases j<;>simp⟩,
  ⟨![1,0,0],funext λ ⟨i,j⟩=>by rw[a];simp only[y6];split_ifs<;>fin_cases j<;>simp⟩⟩
lemma QF (o:zg L) (d:∀ T∈L,∀ j,T (1,j)=T (2,j)) {e f:ze} (g:e∈L) (h:f∈L) (i:∀ k,e (1,k)=if k=2 then 1 else 0) (l:∀ k,f (1,k)=if k=3 then 1 else 0) (c:∀ T∈L,T (1,0)=0/\T (1,1)=0) {r:Fin 4} (m:r=0\/r=3) (b:y6 r ![0,0,1,-1]∈L/\y6 r ![1,1,0,-2]∈L):False:=by
 have n:∀ v,∀ j,y6 r v (1,j)=0:=λ v j=>by rcases m with rfl|rfl<;>simp[y6]
 have D:=λ v (b:y6 r v∈L) T (a:T∈L) t=>(Zr o d a b (n v) t).2;rcases m with rfl|rfl
 . refine QA 3 g h i l c λ T a t=>⟨?_,?_⟩
   . have:=D _ b.1 T a t;simp[ys,y6] at this⊢;linear_combination this
   . have:=D _ b.2 T a t;simp[ys,y6] at this⊢;linear_combination this
 . refine QA 0 g h i l c λ T a t=>⟨?_,?_⟩
   . have:=D _ b.1 T a t;simp[ys,y6] at this⊢;linear_combination this
   . have:=D _ b.2 T a t;simp[ys,y6] at this⊢;linear_combination this
open LinearMap in
lemma QG (g:zg L) (c:∀ T∈L,∀ j,T (1,j)=T (2,j)) (d:finrank KD (L⊓ker (z9 1):Submodule KD ze)=3) (r s:Fin 4) (h:r=0/\s=3\/r=3/\s=0) (e:∀ Y∈L⊓ker (z9 1),∀ j,Y (s,j)=0):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=Qz g inf_le_left d.ge r λ T b i j f=>by
 obtain⟨-,a⟩:=jP c b;rcases h with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>fin_cases i<;>simp at f⊢
 exacts[(a j).1,(a j).2,e T b j,e T b j,(a j).1,(a j).2]
open LinearMap in
lemma WI (i:zg L) (h5:finrank KD L=5) (b:∀ T∈L,∀ j,T (1,j)=T (2,j)) {E F:ze} (y:E∈L) (f:F∈L) (z:∀ k,E (1,k)=if k=2 then 1 else 0) (A:∀ k,F (1,k)=if k=3 then 1 else 0):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=by
 have B:finrank KD (L⊓ker (z9 1):Submodule KD ze)=3:=by have:=zW (z9 1) L;have:=x7 i b;have:=Zu i b;omega
 have P:∀ T∈L,T (1,0)=0/\T (1,1)=0:=by
  let ψ:(Fin 4->KD) →ₗ[KD] KD × KD:=LinearMap.prod (proj 2) (proj 3);have V:(L.map (z9 1)).map ψ=⊤:=eq_top_iff.2 λ x _=>⟨x.1•z9 1 E+x.2•z9 1 F,Submodule.add_mem _ (smul_mem _ _ ⟨E,y,rfl⟩) (smul_mem _ _ ⟨F,f,rfl⟩),by simp[ψ,zA,z,A]⟩;have W:=zW ψ (L.map (z9 1));rw[V,finrank_top,finrank_prod,finrank_self] at W;have d:L.map (z9 1)⊓ker ψ=⊥:=by rw[←finrank_eq_zero];have:=x7 i b;omega
  intro T X;have hm:z9 1 T-T (1,2)•z9 1 E-T (1,3)•z9 1 F∈L.map (z9 1)⊓ker ψ:=⟨Submodule.sub_mem _ (Submodule.sub_mem _ ⟨T,X,rfl⟩ (smul_mem _ _ ⟨E,y,rfl⟩)) (smul_mem _ _ ⟨F,f,rfl⟩),by simp[ψ,zA,z,A]⟩;rw[d] at hm;have:=(mem_bot KD).1 hm;exact⟨by simpa[zA,z,A] using congrFun this 0,by simpa[zA,z,A] using congrFun this 1⟩
 set K:=L⊓ker (z9 1) with a8
 have M:∀ Y∈K,∀ s:KD,∀ T∈L,ys (λ j=>Y (0,j)) (λ k=>s+T (1,k)) (λ j=>Y (3,j))=0:=λ Y a s T X=>(Zr i b X (jP b a).1 (λ j=>((jP b a).2 j).1) s).1;have R:∀ Y∈K,Y (0,0)*Y (3,1)+Y (0,1)*Y (3,0)=0/\Y (0,3)*Y (3,2)+Y (3,3)*Y (0,2)=0/\Y (0,3)*(Y (3,0)+Y (3,1))+Y (3,3)*(Y (0,0)+Y (0,1))=0/\(Y (0,0)+Y (0,1))*Y (3,2)+(Y (3,0)+Y (3,1))*Y (0,2)=0:=λ Y a=>by have q0:=M Y a 0 _ (L.add_mem y f);have q1:=M Y a 1 _ (L.neg_mem (L.add_mem y f));have q2:=M Y a 1 _ (L.neg_mem y);have q3:=M Y a 1 _ (L.neg_mem f);simp[ys,z,A] at q0 q1 q2 q3;grind
 have N:∀ Y∈K,Y (0,0)+Y (0,1)+Y (0,2)+Y (0,3)+(Y (3,0)+Y (3,1)+Y (3,2)+Y (3,3))=0:=λ Y a=>by have:=(Zt i (jP b a).1 (jP b a).2).2;simp only[sum_univ_four] at this;exact this
 let Γ:ze →ₗ[KD] Fin 6->KD:=LinearMap.pi ![zf (0,0)+zf (0,1),zf (0,2),zf (0,3),zf (3,0)+zf (3,1),zf (3,2),zf (3,3)];have Z:∀ Y,Γ Y=0↔Y (0,0)+Y (0,1)=0/\Y (0,2)=0/\Y (0,3)=0/\Y (3,0)+Y (3,1)=0/\Y (3,2)=0/\Y (3,3)=0:=λ Y=>by simp[Γ,funext_iff,Fin.forall_fin_succ,zf]
 have G:finrank KD (K.map Γ)≤1 -> False:=λ h=>by
  have hk:finrank KD (K⊓ker Γ:Submodule KD ze)≤1:=by
   have hz:=λ Y (a:Y∈K⊓ker Γ)=>(Z Y).1 (mem_ker.1 a.2);have Q:∀ Y∈K⊓ker Γ,Y (0,0)=0 -> Y (3,0)=0 -> Y=0:=λ Y a d f=>by obtain⟨z0,z1,t,z3,z4,z5⟩:=hz Y a;exact Zw b a.1 λ j=>by fin_cases j<;>grind
   rcases zz (K⊓ker Γ) (zf (0,0)) (zf (3,0)) (λ Y a=>by obtain⟨z0,-,-,z3,-,-⟩:=hz Y a;have:=(R Y a.1).1;change Y (0,0)*Y (3,0)=0;linear_combination -this/2+Y (0,0)*z3/2+Y (3,0)*z0/2) with h|h
   . exact QC _ (zf (3,0)) λ Y a f=>Q Y a (h Y a) f
   . exact QC _ (zf (0,0)) λ Y a d=>Q Y a d (h Y a)
  have:=zW Γ K;omega
 have C:K≤L:=inf_le_left;by_cases H:∃ Y1∈K,∃ Y2∈K,Y1 (0,3)*Y2 (3,3)-Y2 (0,3)*Y1 (3,3)≠0
 . exfalso;obtain⟨Y1,W,Y2,a3,hD⟩:=H;obtain⟨f1,l,f2,m,g1,g2,g3,g4⟩:=QB K (zf (0,3)) (zf (3,3)) W a3 hD;obtain⟨k,hk⟩:=yF K (zf (0,3)) (zf (3,3)) (zf (0,2)) (zf (3,2)) l m g1 g2 g3 g4 λ Y a=>(R Y a).2.1;obtain⟨k',S⟩:=yF K (zf (0,3)) (zf (3,3)) (zf (0,0)+zf (0,1)) (zf (3,0)+zf (3,1)) l m g1 g2 g3 g4 λ Y a=>(R Y a).2.2.1;have p1:=N _ l;have p2:=N _ m;have a1:=hk _ l;have a2:=hk _ m;have b1:=S _ l;have b2:=S _ m;simp only[zf,proj_apply,LinearMap.add_apply] at g1 g2 g3 g4 a1 a2 b1 b2;grind
 push Not at H;by_cases D:∃ c∈K,c (0,3)≠0
 . obtain⟨c,I,a4⟩:=D
   have o:∀ Y∈K,Y (3,3)=c (3,3)/c (0,3)*Y (0,3):=by grind
   set κ:=c (3,3)/c (0,3);have J:=λ (g:ze →ₗ[KD] KD) (hg:∀ Y∈K,zf (0,3) Y*g Y=0)=>(zz K (zf (0,3)) g hg).resolve_left λ h=>a4 (h c I);have t:=J (zf (3,2)+κ•zf (0,2)) λ Y a=>by have:=(R Y a).2.1;rw[o Y a] at this;simp only[LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,zf,proj_apply];linear_combination this
   have q:=J (zf (3,0)+zf (3,1)+κ•(zf (0,0)+zf (0,1))) λ Y a=>by have:=(R Y a).2.2.1;rw[o Y a] at this;simp only[LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,zf,proj_apply];linear_combination this
   simp only[LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,zf,proj_apply] at t q;by_cases hκ:κ=0
   . rw[hκ] at t q o;simp only[zero_mul,add_zero] at t q o
     rcases zz K (zf (3,0)) (zf (0,1)-zf (0,0)) (λ Y a=>by have:=(R Y a).1;change Y (3,0)*(Y (0,1)-Y (0,0))=0;linear_combination this-Y (0,0)*q Y a) with h|h
     . exact QG i b B 0 3 (Or.inl ⟨rfl,rfl⟩) λ Y a j=>by have c0:Y (3,0)=0:=h Y a;fin_cases j<;>grind
     . exfalso
       refine QF i b y f z A P (Or.inl rfl) ((QE B.ge (by decide:(0:Fin 4)≠3) λ Y a=>?_).imp (λ x=>C x) λ x=>C x);have a9:Y (0,1)=Y (0,0):=by have:=h Y a;change Y (0,1)-Y (0,0)=0 at this;linear_combination this
       obtain⟨-,a5⟩:=jP b a;grind
   . exfalso;apply G
     let ψ:ze →ₗ[KD] KD × KD:=LinearMap.prod (zf (0,0)+zf (0,1)+zf (0,2)) (zf (0,3));refine(QD K Γ ψ λ Y a d=>(Z Y).2 ?_).trans ?_
     . have u:Y (0,0)+Y (0,1)+Y (0,2)=0:=congrArg Prod.fst d;have v:Y (0,3)=0:=congrArg Prod.snd d;grind
     . have a6:K.map ψ≠⊤:=λ e=>by
        obtain⟨Y,a,U⟩:=(e ▸ mem_top:((1:KD),(1:KD))∈K.map ψ);have u:Y (0,0)+Y (0,1)+Y (0,2)=1:=congrArg Prod.fst U;have v:Y (0,3)=1:=congrArg Prod.snd U;have:(2:KD)=0:=by linear_combination N Y a-q Y a-t Y a-o Y a-(1-κ)*u-(1+κ)*v
        norm_num at this
       have:=finrank_lt a6;simp at this;omega
 push Not at D;by_cases O:∃ c∈K,c (3,3)≠0
 . obtain⟨c,I,a7⟩:=O
   have J:=λ (g:ze →ₗ[KD] KD) (hg:∀ Y∈K,zf (3,3) Y*g Y=0)=>(zz K (zf (3,3)) g hg).resolve_left λ h=>a7 (h c I);have t:=J (zf (0,2)) λ Y a=>by have:=(R Y a).2.1;rw[D Y a,zero_mul,zero_add] at this;exact this
   have q:=J (zf (0,0)+zf (0,1)) λ Y a=>by have:=(R Y a).2.2.1;rw[D Y a,zero_mul,zero_add] at this;exact this
   simp only[LinearMap.add_apply,zf,proj_apply] at t q;rcases zz K (zf (0,0)) (zf (3,1)-zf (3,0)) (λ Y a=>by have:=(R Y a).1;change Y (0,0)*(Y (3,1)-Y (3,0))=0;linear_combination this-Y (3,0)*q Y a) with h|h
   . exact QG i b B 3 0 (Or.inr ⟨rfl,rfl⟩) λ Y a j=>by have a0:Y (0,0)=0:=h Y a;fin_cases j<;>grind
   . exfalso
     refine QF i b y f z A P (Or.inr rfl) ((QE B.ge (by decide:(3:Fin 4)≠0) λ Y a=>?_).imp (λ x=>C x) λ x=>C x);have b0:Y (3,1)=Y (3,0):=by have:=h Y a;change Y (3,1)-Y (3,0)=0 at this;linear_combination this
     obtain⟨-,a5⟩:=jP b a;grind
 push Not at O;exfalso;apply G;let Γ2:ze →ₗ[KD] (Fin 2->KD) × (Fin 2->KD):=LinearMap.prod (LinearMap.pi ![zf (0,0)+zf (0,1),zf (0,2)]) (LinearMap.pi ![zf (3,0)+zf (3,1),zf (3,2)]);refine(QD K Γ Γ2 λ Y a d=>(Z Y).2 ?_).trans ?_
 . have u:=congrFun (congrArg Prod.fst d);have v:=congrFun (congrArg Prod.snd d);exact⟨u 0,u 1,D Y a,v 0,v 1,O Y a⟩
 . have:=Qx (n:=2) (by norm_num) (K.map Γ2) λ x hx=>by
    obtain⟨Y,a,rfl⟩:=hx;have p:=N Y a;have w:=(R Y a).2.2.2;rw[D Y a,O Y a] at p;simp[Γ2,dotProduct,sum_univ_two,zf];grind
   omega
lemma WJ (c:zg L) (a:∀ T∈L,∀ j,T (1,j)=T (2,j)) {T:ze} (b:T∈L) {s:KD} {k:Fin 4} (d:∀ j,s+T (1,j)=if j=k then 1 else 0):s=0:=by
 have h:=(Zq (λ i j=>s+T (i,j)) λ j=>by simp[a T b j]).symm.trans (qP c b s);have e:ys (λ j=>s+T (0,j)) (λ j=>s+T (1,j)) (λ j=>s+T (3,j))=0:=by rw[show(λ j=>s+T (1,j))=λ j=>if j=k then 1 else 0 from funext d];fin_cases k<;>simp[ys]
 grind
lemma WK:∀ p q:Fin 4,p≠q->(swap 2 p*swap 3 (swap 2 p q)) 2=p/\(swap 2 p*swap 3 (swap 2 p q)) 3=q:=by decide
lemma QH (σ:Perm (Fin 4)) (h:∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L.map (zq 1 σ:ze →ₗ[KD] ze)):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=by have⟨r,b⟩:=h;refine⟨r,λ w c=>?_⟩;have⟨X,d,a⟩:=b (w∘σ) (by rw[←c];exact Equiv.sum_comp σ w);suffices e:y6 r w=X from e ▸ d;funext ⟨i,j⟩;have:=congrFun a (i,σ.symm j);simp only[LinearEquiv.coe_coe,zy,Perm.one_apply,apply_symm_apply,y6,Function.comp_apply] at this;rw[this];rfl
open LinearMap in
lemma WM (hL:zg L) (h5:finrank KD L=5) (hrow:∀ T∈L,∀ j,T (1,j)=T (2,j)):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0 -> y6 r w∈L:=by
 have a0:finrank KD (L.map (z9 1))=2:=by have:=zW (z9 1) L;have:=x7 hL hrow;have:=Zu hL hrow;omega
 set P:=L.map (z9 1);have A:(λ _=>(1:KD))∉P:=qg hL 1;have m:finrank KD (P⊔span KD {λ _=>(1:KD)}:Submodule KD (Fin 4->KD))=3:=by have a:=finrank_lt_finrank_of_lt (IsConcreteLE.lt_iff_le_and_exists.2 ⟨(le_sup_left:P≤P⊔span KD {λ _=>(1:KD)}),_,mem_sup_right (mem_span_singleton_self _),A⟩);have b:=finrank_sup_add_finrank_inf_eq P (span KD {λ _=>(1:KD)});rw[finrank_span_singleton λ h=>by simpa using congrFun h 0] at b;omega
 set Q:=P⊔span KD {λ _=>(1:KD)};have⟨v,O⟩:∃ v,v∉Q:=by by_contra! h;have:=eq_top_iff'.2 h;rw[this,finrank_top] at m;simp at m
 have⟨f,R,B⟩:=exists_dual_map_eq_bot_of_notMem O inferInstance;have C:∀ y∈Q,f y=0:=λ y e=>by have:f y∈Q.map f:=⟨y,e,rfl⟩;rw[B] at this;simpa using this
 have D:Q=ker f:=by refine eq_of_le_of_finrank_le (λ y e=>C y e) ?_;have:=f.finrank_range_add_finrank_ker;have S:LinearMap.range f=⊤:=range_eq_top.2 λ c=>⟨(c/f v)•v,by simp[R]⟩;rw[S,finrank_top,finrank_self,finrank_fin_fun] at this;omega
 set μ:Fin 4->KD:=λ k=>f λ j=>if k=j then 1 else 0
 have E:∀ y,f y=∑ k,μ k*y k:=λ y=>by rw[pi_apply_eq_sum_univ f y];simp[μ,mul_comm]
 have F:∀ y:Fin 4->KD,∑ k,μ k*y k=0->∃ s:KD,∃ T∈L,y=λ k=>s+T (1,k):=λ y e=>by have:y∈Q:=D ▸ mem_ker.2 ((E y).trans e);obtain⟨_,⟨T,l,rfl⟩,w,U,rfl⟩:=Submodule.mem_sup.1 this;obtain⟨c,rfl⟩:=mem_span_singleton.1 U;exact⟨c,T,l,funext λ k=>by simp[zA,add_comm]⟩
 have n:∀ p,μ p=0->∃ T∈L,∀ k,T (1,k)=if k=p then 1 else 0:=λ p d=>by have⟨s,T,l,o⟩:=F (λ k=>if k=p then 1 else 0) (by simp[d]);have V:=λ j=>(congrFun o j).symm;obtain rfl:=WJ hL hrow l V;grind
 have g:∀ σ:Perm (Fin 4),∀ T∈L.map (zq 1 σ:ze →ₗ[KD] ze),∀ j,T (1,j)=T (2,j):=by rintro σ _ ⟨X,W,rfl⟩ j;exact hrow X W (σ j)
 by_cases t:∃ p q:Fin 4,p≠q/\μ p=0/\μ q=0
 . have⟨p,q,G,d,u⟩:=t
   have⟨H,I,Y⟩:=n p d;have⟨J,K,Z⟩:=n q u;have⟨σ,M,N⟩:∃ σ:Perm (Fin 4),σ 2=p/\σ 3=q:=⟨_,WK p q G⟩;refine QH σ (WI (zH hL 1 σ) ((zF L 1 σ).trans h5) (g σ) ⟨H,I,rfl⟩ ⟨J,K,rfl⟩ (λ k=>?_) λ k=>?_)
   . change H (1,σ k)=_;simp only[Y,←M,σ.injective.eq_iff]
   . change J (1,σ k)=_;simp only[Z,←N,σ.injective.eq_iff]
 push Not at t;have⟨p,d⟩:∃ p:Fin 4,∀ q,q≠p->μ q≠0:=by
  by_cases x:∃ p,μ p=0
  . have⟨p,d⟩:=x;exact⟨p,λ q u h=>t q p u h d⟩
  . push Not at x;exact⟨3,λ q _=>x q⟩
 have z:∀ i,i≠3 -> swap 3 p i≠p:=by grind
 refine QH (swap 3 p) (WH (zH hL 1 _) ((zF L 1 _).trans h5) (g _) (λ k=>μ (swap 3 p k)) (d _ (z 0 (by decide))) (d _ (z 1 (by decide))) (d _ (z 2 (by decide))) λ y e=>?_);have⟨s,T,l,o⟩:=F (y∘(swap 3 p).symm) (by rw[←e];exact(Equiv.sum_comp (swap 3 p) _).symm.trans (by simp));refine⟨s,_,⟨T,l,rfl⟩,funext λ k=>?_⟩;have:=congrFun o (swap 3 p k);simp only[Function.comp_apply,symm_apply_apply] at this;rw[this];rfl
open LinearMap in
lemma WN (hL:zg L) (h6:finrank KD L=6) (_hA:(λ p:Fin 4 × Fin 4=>if p=(1,0) then (1:KD) else if p=(2,0) then -1 else 0)∈L) (hrow:∀ T∈L,∀ j:Fin 4,j≠0 -> T (1,j)=T (2,j)):∃ r:Fin 4,∀ w:Fin 4->KD,∑ j,w j=0->(λ p:Fin 4 × Fin 4=>if p.1=r then w p.2 else 0)∈L:=by
 have k:=zW (zf (1,0)-zf (2,0)) L;have l:=(finrank_le (L.map (zf (1,0)-zf (2,0)))).trans (finrank_self KD).le;have⟨m,a,d⟩:=jV (L⊓ker (zf (1,0)-zf (2,0))) (n:=5) (by omega);have⟨r,e⟩:=WM (λ t f=>hL t (a f).1) d λ T g j=>by
  have⟨b,h⟩:=a g;by_cases c:j=0
  . subst c;have:=mem_ker.1 h;change T (1,0)-T (2,0)=0 at this;linear_combination this
  . exact hrow T b j c
 exact⟨r,λ w i=>(a (e w i)).1⟩
lemma yR (hL:zg L) (h6:finrank KD L=6) (hA:(λ p:Fin 4 × Fin 4=>if p=(1,0) then (1:KD) else if p=(2,0) then -1 else 0)∈L) (hrow:∀ T∈L,∀ j:Fin 4,j≠0 -> T (1,j)=T (2,j)):False:=by have⟨r,a⟩:=WN hL h6 hA hrow;have:=wL hL r a;omega
noncomputable def y4:ze →ₗ[KD] KD where
 toFun X:=(∑ p,X p)/16
 map_add' X Y:=by simp only[Pi.add_apply,sum_add_distrib];ring
 map_smul' c X:=by simp only[Pi.smul_apply,smul_eq_mul,RingHom.id_apply,←Finset.mul_sum];ring
def zP (L:Submodule KD ze):Submodule KD ze:=L⊔span KD {qk}
lemma yf (hL:zg L) {T:ze} (hT:T∈L):y4 T=0:=by have:=(qb hL hT).1;simp only[qY] at this;simp[y4,this]
lemma jI:y4 qk=1:=by simp[y4,qk]
lemma yG (hL:zg L) {X:ze} (hX:X∈zP L):ql (λ i j=>X (i,j))=24*y4 X^4:=by obtain⟨T,a,_,b,rfl⟩:=Submodule.mem_sup.1 hX;obtain⟨c,rfl⟩:=mem_span_singleton.1 b;have h:=qP hL a c;rw[map_add,map_smul,yf hL a,jI,smul_eq_mul,mul_one,zero_add,←h];congr 1;funext i j;simp[qk];ring
def wM (X:ze) (a b:Fin 4):KD:=zo λ c d=>X (z8 a c,z8 b d)
lemma QI (f:zg L) {X Z:ze} (g:X∈zP L) (h:Z∈L) (i:∀ a b,b≠0 -> Z (a,b)=0):∑ a,Z (a,0)*wM X a 0=0:=by
 have e:=yG f ((zP L).add_mem g (mem_sup_left h));have j:=yG f g;rw[map_add,yf f h,add_zero,←j,ye _ 0,ye _ 0] at e;have k:∀ a,(zo λ c d=>X (z8 a c,z8 0 d)+Z (z8 a c,z8 0 d))=wM X a 0:=λ a=>by simp only[wM];congr 1;funext c d;simp[i _ _ (by fin_cases d<;>decide:z8 0 d≠0)]
 simp only[Pi.add_apply] at e;simp only[k,add_mul,sum_add_distrib] at e;simp only[wM] at e⊢;linear_combination e
def kv (z:Fin 4->KD) (W:ze):KD:=∑ a,z a*wM W a 0
lemma WO (X Y:ze) (z:Fin 4->KD) (k:Fin 3) (b:∀ j,j≠0 -> X (0,j)=0) (c:∀ j,Y (0,j)=if j=z8 0 k then 1 else 0) (l:z 0=0):8*(kv z (X+Y)-kv z (X-Y))-(kv z (X+(2:KD)•Y)-kv z (X-(2:KD)•Y))=12*∑ a,z (z8 0 a)*zn (z7 0 0 X) a k:=by
 have g:=b 1 (by decide);have h:=b 2 (by decide);have i:=b 3 (by decide);have d:=c 1;have e:=c 2;have f:=c 3;fin_cases k<;>simp[z8] at d e f <;>
 simp[kv,wM,zs,zK,z8,z6,sum_univ_four,sum_univ_three,zt,g,h,i,d,e,f,l]<;>ring
lemma WP {n:ℕ} (a b:Fin n->KD) (h:∀ t:KD,∏ i,(a i+b i*t)=0):∃ i,a i=0/\b i=0:=by
 classical
 have f:(∏ i,(Polynomial.C (a i)+Polynomial.C (b i)*Polynomial.X))=0:=Polynomial.funext λ t=>by simp[Polynomial.eval_prod,h t]
 obtain⟨i,-,d⟩:=prod_eq_zero_iff.1 f;have c:=congrArg (Polynomial.eval 0) d;have e:=congrArg (Polynomial.eval 1) d;simp at c e;exact⟨i,c,by simpa[c] using e⟩
lemma yS {E:Type} [AddCommGroup E] [Module KD E] (K:Submodule KD E) {n:ℕ} (c:Fin n->KD) (φ:Fin n -> E →ₗ[KD] KD) (h:∀ S∈K,∏ i,(c i+φ i S)=0):∃ i,c i=0/\∀ S∈K,φ i S=0:=by
 have⟨x,a,b⟩:=kb K φ;have⟨i,d,e⟩:=WP c (λ i=>φ i x) λ t=>by simpa[mul_comm] using h _ (K.smul_mem t a)
 exact⟨i,d,b i e⟩
lemma kc {E:Type} [AddCommGroup E] [Module KD E] (K:Submodule KD E) {c A:KD} (d:A≠0) (φ:E →ₗ[KD] KD) (F:E->KD) (h:∀ S∈K,(c+φ S)*F S=A):∀ S∈K,φ S=0:=λ S a=>by by_contra b;have:=h _ (K.smul_mem (-c/φ S) a);rw[map_smul,smul_eq_mul,div_mul_cancel₀ _ b] at this;simp at this;exact d this.symm
lemma jQ (hL:zg L) {X:ze} (hX:X∈zP L) (h0:∀ j,X (0,j)=0):X∈L:=by
 obtain⟨T,b,_,d,rfl⟩:=Submodule.mem_sup.1 hX;obtain⟨c,rfl⟩:=mem_span_singleton.1 d;by_cases a:c=0
 . simpa[a] using b
 . exact absurd ⟨(-c⁻¹)•T,L.smul_mem _ b,funext λ j=>by have:=h0 j;simp[qk] at this;simp[zA,show T (0,j) = -c by linear_combination this,a]⟩ (qg hL 0)
lemma QJ (d:zg L) (f:finrank KD (L.map (z9 0))=3) {l:(Fin 4->KD) →ₗ[KD] KD} (g:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a):∃ M:Fin 4 -> ze,∀ k,M k∈zP L/\(∀ j,M k (0,j)=if j=k then 1 else 0)/\y4 (M k)=l (Pi.single k 1):=by
 have e:=(qu d f).1;choose a T b c using λ k:Fin 4=>e (Pi.single k 1);refine⟨λ k=>T k+a k•qk,λ k=>⟨add_mem_sup (b k) (smul_mem _ _ (mem_span_singleton_self _)),λ j=>?_,?_⟩⟩
 . have:=congrFun (c k) j;simp[Pi.single_apply] at this;simp[qk,this,add_comm]
 . rw[map_add,map_smul,yf d (b k),jI,c k,g _ _ (b k)];simp
lemma QK (d:zg L) {a:ze} (f:a∈zP L) (g:∀ j,a (0,j)=if j=0 then 1 else 0) {S:ze} (b:S∈zh L 0):zo (z7 0 0 (a+S))=24*y4 a^4:=by have c:∀ j,S (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 b.2) j;have e:=yG d ((zP L).add_mem f (mem_sup_left b.1));rw[map_add,yf d b.1,add_zero,yd _ 0] at e;rw[←e,sum_univ_four];simp[g,c];rfl
lemma QL (u:zg L) {d f:ze} (v:d∈zP L) (w:∀ j,d (0,j)=if j=0 then 1 else 0) (k:Fin 3) (m:f∈zP L) (n:∀ j,f (0,j)=if j=z8 0 k then 1 else 0) {S:ze} (o:S∈zh L 0) {Z:ze} (x:Z∈L) (p:∀ a b,b≠0 -> Z (a,b)=0) (g:Z (0,0)=0):∑ a,Z (z8 0 a,0)*zn (z7 0 0 (d+S)) a k=0:=by
 have h:∀ j,S (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 o.2) j;have q:d+S∈zP L:=(zP L).add_mem v (mem_sup_left o.1);have e:=WO (d+S) f (λ a=>Z (a,0)) k (λ j r=>by simp[w,h,r]) n g;have i:∀ c:KD,kv (λ a=>Z (a,0)) (d+S+c•f)=0:=λ c=>QI u ((zP L).add_mem q ((zP L).smul_mem c m)) x p;have l:∀ c:KD,kv (λ a=>Z (a,0)) (d+S-c•f)=0:=λ c=>by rw[sub_eq_add_neg,←neg_smul];exact i _
 have s:=i 1;have t:=l 1;rw[one_smul] at s t;grind
lemma qU (f:Fin 3->KD) (a:Fin 3):∑ r,f r=f a+f (z6 a 0)+f (z6 a 1):=by fin_cases a<;>simp[sum_univ_three,z6]<;>ring
lemma w5:∀ c c':Fin 3,c≠c'->∃ k,(c=z6 k 0/\c'=z6 k 1)\/(c=z6 k 1/\c'=z6 k 0):=by decide
lemma zN:∀ a:Fin 3,a≠z6 a 0/\a≠z6 a 1/\z6 a 0≠z6 a 1:=by decide
lemma WQ (W S:zx) (a u:Fin 3) (g:∀ c,∑ r,W r c≠0) (k:∑ r,S r u=0) (t:∀ r c c',c≠c' -> W r c*W r c'=0) (hx:∀ r c c',c≠c' -> S r c*W r c'=0):S a u=0:=by
 have⟨l,m,n⟩:=zN a;have⟨o,p,q⟩:=zN u;set b:=zV a 0;set s:=zV a 1;set v:=zV u 0;set d:=zV u 1;rw[qU _ a] at k;by_contra h;have i:W a v=0:=by grind
 have e:W a d=0:=by grind
 have j:=g v;have f:=g d;rw[qU _ a,i] at j;rw[qU _ a,e] at f;grind
lemma WR (W S:zx) (i:∀ c,∑ r,W r c≠0) (j:∀ c,∑ r,S r c=0) (k:(∀ r c c',c≠c' -> W r c*W r c'=0)\/(∀ r c c',c≠c' -> W r c*W r c'≠0)) (m:∀ r c c',c≠c' -> S r c*S r c'=0) (l:∀ r c c',c≠c' -> W r c*S r c'+S r c*W r c'=0):S=0:=by
 rcases k with b|d
 . have f:∀ r c c',c≠c' -> S r c*W r c'=0:=λ r c c' h=>pow_eq_zero_iff (n:=2) (by norm_num) |>.1 (by
    linear_combination S r c*W r c'*l r c c' h-S r c*S r c'*b r c c' h)
   exact funext λ a=>funext λ u=>WQ W S a u i (j u) b f
 . funext r c
   obtain⟨-,g,-⟩:=zN c;have:=d r c _ g;have e:S r c^2*W r (zV c 1)=0:=by grind
   simpa[(mul_ne_zero_iff.1 this).2] using e
lemma WS (C:zx) (r k:Fin 3):zn C (z6 r 0) k+zn C (z6 r 1) k=C r (z6 k 0)*(∑ b,C b (z6 k 1)-C r (z6 k 1))+C r (z6 k 1)*(∑ b,C b (z6 k 0)-C r (z6 k 0)):=by fin_cases r<;>fin_cases k<;>simp[zK,z6,sum_univ_three]<;>ring
lemma WT (s:Fin 3->KD) (k:Fin 3):s (z6 k 0)*s (z6 k 1)*s k=s 0*s 1*s 2:=by fin_cases k<;>simp[z6]<;>ring
lemma WU (B d:zx) {g:KD} (z:g≠0) (p:∀ t:KD,zo (B+t•d)=g) (A:∀ t:KD,∀ k a a',zn (B+t•d) a k=zn (B+t•d) a' k):d=0:=by
 set s:Fin 3->KD:=λ k=>∑ r,B r k;have j:∀ t:KD,∀ k,(s k+t*∑ r,d r k)*zn (B+t•d) 0 k=g:=λ t k=>by rw[←p t,jc _ k,show s k+t*∑ r,d r k=∑ i,(B+t•d) i k by simp[s,sum_add_distrib,Finset.mul_sum],Finset.sum_mul];grind
 have n:∀ k,∑ r,d r k=0:=λ k=>by by_contra h;have:=j (-s k/∑ r,d r k) k;grind
 have m:∀ k,s k≠0:=λ k h=>by have:=j 0 k;simp[h] at this;exact z this.symm
 have q:∀ t:KD,∀ a k,zn (B+t•d) a k=g/s k:=λ t a k=>by rw[A t k a 0,eq_div_iff (m k)];have:=j t k;rw[n k] at this;linear_combination this
 set W:zx:=λ r c=>2*B r c-s c;have u:∀ r k,∀ t:KD,(W r (zV k 0)+2*t*d r (zV k 0))*(W r (zV k 1)+2*t*d r (zV k 1))=s (zV k 0)*s (zV k 1)-4*g/s k:=λ r k t=>by
  have e:=WS (B+t•d) r k;rw[q,q] at e;have v:∀ c,∑ b,(B+t•d) b c=s c:=λ c=>by simp[s,sum_add_distrib,←Finset.mul_sum,n c]
  rw[v,v] at e;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul] at e;grind
 have o:∀ r k,W r (zV k 0)*W r (zV k 1)=s (zV k 0)*s (zV k 1)-4*g/s k/\W r (zV k 0)*d r (zV k 1)+d r (zV k 0)*W r (zV k 1)=0/\d r (zV k 0)*d r (zV k 1)=0:=λ r k=>by
  have⟨a,b,c⟩:=qc (W r (zV k 0)*W r (zV k 1)-(s (zV k 0)*s (zV k 1)-4*g/s k)) (2*(W r (zV k 0)*d r (zV k 1)+d r (zV k 0)*W r (zV k 1))) (4*(d r (zV k 0)*d r (zV k 1))) λ t=>by linear_combination u r k t
  grind
 have y:∀ r k,W r (zV k 0)*W r (zV k 1)*s k=s 0*s 1*s 2-4*g:=λ r k=>by rw[(o r k).1,sub_mul,div_mul_cancel₀ _ (m k),WT]
 have l:∀ P:Fin 3 -> Fin 3 -> Prop,(∀ c f,P c f -> P f c)->(∀ k,P (zV k 0) (zV k 1))->∀ c f,c≠f -> P c f:=λ P p w c f h=>by obtain⟨k,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩:=w5 c f h;exacts[w k,p _ _ (w k)]
 apply WR W d (λ c=>by simp only[W,sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,card_univ,Fintype.card_fin];intro h;apply m c;simp only[s] at h⊢;linear_combination -h) n
 . by_cases x:s 0*s 1*s 2-4*g=0
   . left;intro r;exact l (λ c f=>W r c*W r f=0) (λ c f h=>by rw[mul_comm];exact h) λ k=>(mul_eq_zero.1 ((y r k).trans x)).resolve_right (m k)
   . right;intro r;exact l (λ c f=>W r c*W r f≠0) (λ c f h=>by rw[mul_comm];exact h) λ k h=>x (by grind)
 . intro r;exact l (λ c f=>d r c*d r f=0) (λ c f h=>by rw[mul_comm];exact h) λ k=>(o r k).2.2
 . intro r;exact l (λ c f=>W r c*d r f+d r c*W r f=0) (λ c f h=>by linear_combination h) λ k=>(o r k).2.1
abbrev zu:=Fin 3->KD
lemma x9 (q:zu →ₗ[KD] zu →ₗ[KD] KD) (e f:Fin 3 -> zu) (b:∀ i j,q (e i) (f j)=if i=j then 1 else 0) (x:zu):x=∑ i,q x (f i)•e i:=by
 let Φ:zu →ₗ[KD] zu:=LinearMap.pi λ i=>q.flip (f i);have a:∀ c:zu,Φ (∑ i,c i•e i)=c:=λ c=>funext λ j=>by simp[Φ,b]
 have d:Function.Injective Φ:=LinearMap.injective_iff_surjective.2 λ c=>⟨_,a c⟩;exact d (by rw[a];rfl)
lemma kw {E:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] (S:Submodule KD E) (f:E →ₗ[KD] KD) (h:∀ M∈S,f M=0 -> M=0):finrank KD S≤1:=by have e:=zW f S;rw[(Submodule.eq_bot_iff _).2 λ M a=>h M (Submodule.mem_inf.1 a).1 (Submodule.mem_inf.1 a).2,finrank_bot] at e;have:=finrank_le (S.map f);rw[finrank_self] at this;omega
open LinearMap in
lemma w7 (q:zu →ₗ[KD] zu →ₗ[KD] KD) (hqn:∀ x,(∀ y,q x y=0) -> x=0):ker q=⊥:=(Submodule.eq_bot_iff _).2 λ x a=>hqn x λ y=>by rw[mem_ker.1 a];rfl
lemma jj (z:KD):∃ w:KD,w^2=z:=by
 set a:=z.re;set b:=z.im;set r:=Real.sqrt (a^2+b^2);have l:r^2=a^2+b^2:=Real.sq_sqrt (by positivity);have j:0≤r:=Real.sqrt_nonneg _;have k:|a|≤r:=by rw[←Real.sqrt_sq_eq_abs];exact Real.sqrt_le_sqrt (by nlinarith)
 have d:0≤(r+a)/2:=by grind
 have f:0≤(r-a)/2:=by grind
 set x:=Real.sqrt ((r+a)/2);set y:=Real.sqrt ((r-a)/2);have g:x^2=(r+a)/2:=Real.sq_sqrt d;have h:y^2=(r-a)/2:=Real.sq_sqrt f;have c:x*y=|b|/2:=by
  have e:(x*y)^2=(|b|/2)^2:=by grind
  exact(pow_left_inj₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity) (by norm_num)).1 e
 refine⟨⟨x,if 0≤b then y else -y⟩,Complex.ext ?_ ?_⟩
 . simp only[sq,Complex.mul_re];split_ifs<;>nlinarith[g,h]
 . simp only[sq,Complex.mul_im];split_ifs with i
   . rw[abs_of_nonneg i] at c;linarith
   grind
open LinearMap in
lemma WV (q:zu →ₗ[KD] zu →ₗ[KD] KD) (f:∀ x y,q x y=q y x) (b:∀ x,(∀ y,q x y=0) -> x=0) {u:zu} (k:u≠0):∃ v,q v v=1/\q u v=0:=by
 have⟨y,g⟩:∃ y,q u y≠0:=by by_contra! h;exact k (b u h)
 set U:=ker (q u);have i:finrank KD U=2:=by
  have e:=(q u).finrank_range_add_finrank_ker;have:LinearMap.range (q u)=⊤:=by refine eq_top_iff.2 λ c _=>⟨(c/q u y)•y,?_⟩;simp[map_smul,div_mul_cancel₀ _ g]
  rw[this,finrank_top,finrank_self,finrank_fin_fun] at e;simp only[U];omega
 have⟨a,d,l⟩:∃ a∈U,q a a≠0:=by by_contra! h;have:=qr q U U (yr q f U h);rw[w7 q b,inf_bot_eq,finrank_bot,i] at this;simp at this
 have⟨ρ,j⟩:=jj (q a a);have m:ρ≠0:=by grind
 refine⟨ρ⁻¹•a,?_,?_⟩
 . simp only[map_smul,LinearMap.smul_apply,smul_eq_mul,←j];field_simp
 . simp[mem_ker.1 d]
lemma QM (q:zu →ₗ[KD] zu →ₗ[KD] KD) (c:∀ x y,q x y=q y x) (g:∀ x,(∀ y,q x y=0) -> x=0) {u v:zu} (m:u≠0) (d:q u u=0) (i:q v v=1) (e:q u v=0):∃ w,q u w=1/\q w w=0/\q v w=0:=by
 have⟨y,j⟩:∃ y,q u y≠0:=by by_contra! h;exact m (g u h)
 set b:=(q u y)⁻¹•y;have k:q u b=1:=by simp[b,j]
 set a:=b-q v b•v;have f:q u a=1:=by simp[a,k,e]
 have l:q v a=0:=by simp[a,i]
 refine⟨a-(q a a/2)•u,?_,?_,?_⟩
 . simp[f,d]
 . simp only[map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,d,c a u,f];ring
 . simp[l,c v u,e]
def jJ (q:zu →ₗ[KD] zu →ₗ[KD] KD) (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (B:Fin 3 -> zu) (S:Submodule KD (Fin 3 -> zu)) (A:KD):Prop :=
 ∀ M∈S,(∀ u v,u≠v -> q (B u+M u) (B v+M v)=0)/\H (B 0+M 0) (B 1+M 1) (B 2+M 2)=A
def jX (q:zu →ₗ[KD] zu →ₗ[KD] KD) (x:zu) (i:Fin 3):(Fin 3 -> zu) →ₗ[KD] KD :=
 (q.flip x).comp (LinearMap.proj i)
lemma vm (q:zu →ₗ[KD] zu →ₗ[KD] KD) (x:zu) (i:Fin 3) (M:Fin 3 -> zu):jX q x i M=q (M i) x:=rfl
lemma kd {q H B S A} (h:jJ q H B S A) {M} (e:M∈S) {u v:Fin 3} (d:u≠v):q (B u) (B v)=0/\q (B u) (M v)+q (M u) (B v)=0/\q (M u) (M v)=0:=by
 have⟨a,b,c⟩:=qc (q (B u) (B v)) (q (B u) (M v)+q (M u) (B v)) (q (M u) (M v)) λ t=>by have:=(h _ (S.smul_mem t e)).1 u v d;simp only[Pi.smul_apply,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at this;linear_combination this
 exact⟨a,b,c⟩
lemma QN {q H B S A} (h:jJ q H B S A) (b:A≠0):B∉S:=λ a=>by have:=(h _ (S.smul_mem (-1) a)).2;simp at this;exact b this.symm
lemma Zx {E:Type} [AddCommGroup E] [Module KD E] (S:Submodule KD E) {A X Y:KD} (a:A≠0) (f g h k:E →ₗ[KD] KD) (H:∀ M∈S,(1+f M)*(1+g M)*((1+h M)*X+k M*Y)=A):X=A/\∀ M∈S,f M=0/\g M=0/\h M*A+k M*Y=0:=by
 have d:X=A:=by simpa using H 0 S.zero_mem
 have e:=kc (c:=1) S a f (λ M=>(1+g M)*((1+h M)*X+k M*Y)) λ M b=>by grind
 have i:=kc (c:=1) S a g (λ M=>(1+f M)*((1+h M)*X+k M*Y)) λ M b=>by grind
 grind
lemma QO (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (g:∀ x y z,H x y z=H y x z) (h:∀ x y z,H x y z=H x z y) (u v:zu) (a b c d e f:KD):H (a•u+d•v) (b•u+e•v) (c•u+f•v)=a*b*c*H u u u+(a*b*f+a*e*c+d*b*c)*H u u v+(a*e*f+d*b*f+d*e*c)*H u v v+d*e*f*H v v v:=by
 have i:H u v u=H u u v:=h _ _ _;have j:H v u u=H u u v:=by grind
 have k:H v u v=H u v v:=g _ _ _;have l:H v v u=H u v v:=by grind
 simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,i,j,k,l];ring
lemma WW:∀ i j k l:Fin 3,i≠k -> j≠k -> i≠j -> l≠k -> l=i\/l=j:=by decide
lemma WX (q:zu →ₗ[KD] zu →ₗ[KD] KD) (d:∀ x y,q x y=q y x) (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (G:∀ x y z,H x y z=H y x z) (I:∀ x y z,H x y z=H x z y) {u v w:zu} (o:q u u=0) (J:q u w=1) (K:q w w=0) (p:q v v=1) (r:q u v=0) (L:q v w=0) {S:Submodule KD (Fin 3 -> zu)} {A:KD} (T:A≠0) (h:jJ q H (λ _=>u) S A):finrank KD S≤1:=by
 have C:=x9 q ![u,v,w] ![w,v,u] (λ i j=>by fin_cases i<;>fin_cases j<;>simp[o,J,K,p,r,L,d w u,d v u,d w v]);simp[sum_univ_three] at C;have N:∀ M∈S,∀ i,q (M i) u=0:=λ M a=>by
  have e:∀ i j,i≠j -> q (M i) u+q (M j) u=0:=λ i j b=>by have:=(kd h a b).2.1;rw[d u] at this;linear_combination this
  have V:q (M 0) u=0:=by linear_combination (e 0 1 (by decide)+e 0 2 (by decide)-e 1 2 (by decide))/2
  grind
 have g:∀ M∈S,∀ i,M i=q (M i) w•u+q (M i) v•v:=λ M a i=>by have:=C (M i);rw[N M a i,zero_smul,add_zero] at this;exact this
 have O:∀ M∈S,∀ i j,i≠j -> q (M i) v*q (M j) v=0:=λ M a i j b=>by have:=(kd h a b).2.2;rw[g M a i,g M a j] at this;simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,o,r,p,d v u] at this;linear_combination this
 have s:∀ i j,i≠j->(∀ M∈S,q (M i) v=0)\/∀ M∈S,q (M j) v=0:=λ i j b=>zz S (jX q v i) (jX q v j) λ M a=>O M a i j b;have U:∀ M∈S,(1+q (M 0) w)*(1+q (M 1) w)*(1+q (M 2) w)*H u u u+((1+q (M 0) w)*(1+q (M 1) w)*q (M 2) v+(1+q (M 0) w)*q (M 1) v*(1+q (M 2) w)+q (M 0) v*(1+q (M 1) w)*(1+q (M 2) w))*H u u v+((1+q (M 0) w)*q (M 1) v*q (M 2) v+q (M 0) v*(1+q (M 1) w)*q (M 2) v+q (M 0) v*q (M 1) v*(1+q (M 2) w))*H u v v+q (M 0) v*q (M 1) v*q (M 2) v*H v v v=A:=λ M a=>by
  have e:∀ i,u+M i=(1+q (M i) w)•u+q (M i) v•v:=λ i=>by
   conv_lhs=>rw[g M a i]
   rw[add_smul,one_smul];abel
  have:=(h M a).2;simp only at this;rw[e 0,e 1,e 2,QO H G I] at this;exact this
 have D:∀ k:Fin 3,(∀ M∈S,q (M k) v=0 -> q (M k) w=0)->(∀ M∈S,∀ j,j≠k -> q (M j) v=0/\q (M j) w=0) -> finrank KD S≤1:=λ k m f=>kw S (jX q v k) λ M a e=>funext λ j=>by
  rw[g M a j];by_cases n:j=k
  . subst n;simp[show q (M j) v=0 from e,m M a e]
  . simp[(f M a j n).1,(f M a j n).2]
 have c:∀ k i j:Fin 3,i≠k -> j≠k -> i≠j->(∀ M∈S,q (M i) v=0)->(∀ M∈S,q (M j) v=0)->(∀ M∈S,(1+q (M i) w)*(1+q (M j) w)*((1+q (M k) w)*H u u u+q (M k) v*H u u v)=A) -> finrank KD S≤1:=λ k i j E F b P n Q=>by
  obtain⟨-,t⟩:=Zx S T (jX q w i) (jX q w j) (jX q w k) (jX q v k) Q;refine D k (λ M a e=>?_) λ M a l R=>?_
  . have:=(t M a).2.2;simp only[vm,e,zero_mul,add_zero] at this;grind
  . rcases WW i j k l E F b R with rfl|rfl
    exacts[⟨P M a,(t M a).1⟩,⟨n M a,(t M a).2.1⟩]
 rcases s 1 2 (by decide) with m|f
 . rcases s 0 2 (by decide) with B|f
   . exact c 2 0 1 (by decide) (by decide) (by decide) B m λ M a=>by grind
   . exact c 0 1 2 (by decide) (by decide) (by decide) m f λ M a=>by grind
 . rcases s 0 1 (by decide) with B|m
   . exact c 1 0 2 (by decide) (by decide) (by decide) B f λ M a=>by grind
   . exact c 0 1 2 (by decide) (by decide) (by decide) m f λ M a=>by grind
open LinearMap in
lemma WY {E:Type} [AddCommGroup E] [Module KD E] (S:Submodule KD E) (b c e:E →ₗ[KD] KD) (h:∀ M∈S,b M^2=c M*e M) (p:¬ ∀ M∈S,b M=0):∃ κ:KD,κ≠0/\∀ M∈S,c M=κ*b M/\κ*e M=b M:=by
 push Not at p;have⟨d,i,j⟩:=p;have q:∀ M∈S,M-(b M/b d)•d∈S⊓ker b:=λ M a=>⟨S.sub_mem a (S.smul_mem _ i),by simp[div_mul_cancel₀ _ j]⟩;have m:∀ f:E →ₗ[KD] KD,(∀ M∈S⊓ker b,f M=0)->∀ M∈S,f M=f d/b d*b M:=λ f r M a=>by have:=r _ (q M a);simp at this;grind
 have n:∀ g:E →ₗ[KD] KD,(∀ M∈S,b M*g M=0)->∀ M∈S,g M=0:=λ g s=>(zz S b g s).resolve_left λ t=>j (t d i);rcases zz (S⊓ker b) c e λ M a=>by have:=h M a.1;rw[mem_ker.1 a.2] at this;linear_combination -this with u|v
 . set κ:=c d/b d
   have o:=m c u;have k:=n (b-κ•e) λ M a=>by simp only[LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul];grind
   have l:κ≠0:=by grind
   exact⟨κ,l,λ M a=>⟨o M a,by have:=k M a;simp at this;linear_combination -this⟩⟩
 . set κ:=e d/b d
   have o:=m e v;have k:=n (b-κ•c) λ M a=>by simp only[LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul];grind
   have l:κ≠0:=by grind
   refine⟨κ⁻¹,inv_ne_zero l,λ M a=>⟨?_,?_⟩⟩
   . have:=k M a;simp at this;field_simp;linear_combination -this
   grind
lemma WZ (q:zu →ₗ[KD] zu →ₗ[KD] KD) (m:∀ x y,q x y=q y x) (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (a0:∀ x y z,H x y z=H y x z) (a1:∀ x y z,H x y z=H x z y) {u v w:zu} (a2:q u u=0) (a3:q u w=1) (a4:q w w=0) (a5:q v v=1) (a6:q u v=0) (a7:q v w=0) {S:Submodule KD (Fin 3 -> zu)} {A:KD} (F:A≠0) (h:jJ q H ![u,u,v] S A):finrank KD S≤1:=by
 have N:=x9 q ![u,v,w] ![w,v,u] (λ i j=>by fin_cases i<;>fin_cases j<;>simp[a2,a3,a4,a5,a6,a7,m w u,m v u,m w v]);simp[sum_univ_three] at N;have qe:∀ x y,q x y=q y w*q x u+q y v*q x v+q y u*q x w:=λ x y=>by
  conv_lhs=>rw[N y]
  simp only[map_add,map_smul,smul_eq_mul]
 set a:Fin 3->(Fin 3 -> zu) →ₗ[KD] KD:=λ i=>jX q w i;set b:Fin 3->(Fin 3 -> zu) →ₗ[KD] KD:=λ i=>jX q v i;set c:Fin 3->(Fin 3 -> zu) →ₗ[KD] KD:=λ i=>jX q u i;have f:∀ M i,M i=a i M•u+b i M•v+c i M•w:=λ M i=>N (M i);have k:∀ M∈S,c 1 M = - c 0 M:=λ M d=>by have:=(kd h d (by decide:(0:Fin 3)≠1)).2.1;simp[m u] at this;simp only[c,vm];linear_combination this
 have g:∀ M∈S,c 2 M = - b 0 M:=λ M d=>by have:=(kd h d (by decide:(0:Fin 3)≠2)).2.1;simp[m u] at this;simp only[b,c,vm];linear_combination this
 have l:∀ M∈S,b 1 M=b 0 M:=λ M d=>by have:=(kd h d (by decide:(1:Fin 3)≠2)).2.1;simp[m u] at this;simp only[b,c,vm] at g⊢;linear_combination this-g M d
 have Q:∀ M∈S,∀ i j,i≠j -> a j M*c i M+b j M*b i M+c j M*a i M=0:=λ M d i j U=>by have:=(kd h d U).2.2;rw[qe] at this;exact this
 have V:=λ M d=>Q M d 0 1 (by decide);have G:=λ M d=>Q M d 0 2 (by decide);have I:=λ M d=>Q M d 1 2 (by decide);have O:=λ M d=>(h M d).2;simp only[cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons] at O;have W:∀ M∈S,(∀ i,a i M=0/\b i M=0/\c i M=0) -> M=0:=λ M d P=>funext λ i=>by rw[f M i,(P i).1,(P i).2.1,(P i).2.2];simp
 by_cases n:∀ M∈S,b 0 M=0
 . have R:∀ M∈S,c 0 M*(a 1 M-a 0 M)=0:=λ M d=>by
    grind
   have X:∀ M∈S,c 0 M*a 2 M=0:=by grind
   by_cases D:∀ M∈S,c 0 M=0
   . have s:∀ M∈S,(1+a 0 M)*(1+a 1 M)*((1+b 2 M)*H u u v+a 2 M*H u u u)=A:=λ M d=>by
      have e0:u+M 0=(1+a 0 M)•u+(0:KD)•v:=by rw[f M 0,n M d,D M d];simp[add_smul]
      have E:u+M 1=(1+a 1 M)•u+(0:KD)•v:=by rw[f M 1,l M d,k M d,n M d,D M d];simp[add_smul]
      have e2:v+M 2=a 2 M•u+(1+b 2 M)•v:=by rw[f M 2,g M d,n M d];simp[add_smul];abel
      have:=O M d;rw[e0,E,e2,QO H a0 a1] at this;linear_combination this
     obtain⟨-,H3⟩:=Zx S F (a 0) (a 1) (b 2) (a 2) s;refine kw S (a 2) λ M d e=>W M d λ i=>?_;have p:b 2 M=0:=by grind
     fin_cases i<;>grind
   . have J:=(zz S (c 0) (a 1-a 0) λ M d=>by
      simpa using R M d).resolve_left D
     have B:=(zz S (c 0) (a 2) X).resolve_left D;have s:∀ M∈S,(1+b 2 M)*((1+a 0 M)^2*H u u v-c 0 M^2*H w w v)=A:=λ M d=>by
      have E:a 1 M=a 0 M:=by have:=J M d;simp at this;linear_combination this
      have:=O M d;rw[f M 0,f M 1,f M 2,E,l M d,k M d,g M d,n M d,B M d] at this;simp only[neg_zero,zero_smul,add_zero,zero_add,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,neg_smul,map_neg,LinearMap.neg_apply] at this;grind
     have p:=kc (c:=1) S F (b 2) _ s;have hX:H u u v=A:=by simpa using s 0 S.zero_mem
     have C:∀ M∈S,a 0 M=0:=λ M d=>by
      obtain⟨-,h1,-⟩:=qc 0 (2*a 0 M*A) (a 0 M^2*A-c 0 M^2*H w w v) λ t=>by have:=s _ (S.smul_mem t d);rw[p _ (S.smul_mem t d),hX] at this;simp only[map_smul,smul_eq_mul] at this;linear_combination this
      simpa[F] using h1
     refine kw S (c 0) λ M d e=>W M d λ i=>?_;have E:a 1 M=0:=by have:=J M d;simp[C M d] at this;exact this
     fin_cases i<;>grind
 . have hs:=(zz S (b 0) ((2:KD)•b 2-a 0-a 1) λ M d=>by
    simp only[LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination G M d+I M d-a 2 M*k M d-b 2 M*l M d-(a 0 M+a 1 M)*g M d).resolve_left n
   have⟨κ,Y,K⟩:=WY S (b 0) (c 0) (a 0-a 1) (λ M d=>by simp only[LinearMap.sub_apply];linear_combination V M d-b 0 M*l M d-a 0 M*k M d) n;have hd:=(zz S (b 0) ((2*κ)•a 2-(a 0-a 1)) λ M d=>by simp only[LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination G M d-I M d-2*a 2 M*(K M d).1+a 2 M*k M d+b 2 M*l M d-(a 0 M-a 1 M)*g M d).resolve_left n;by_contra a8;have⟨M,d,Z,r⟩:=wD (b 0) S (by have:=finrank_le (S.map (b 0));rw[finrank_self] at this;omega);have L:c 0 M=0:=by grind
   have o:a 1 M=a 0 M:=by have:=(K M d).2;rw[r] at this;simp[Y] at this;linear_combination -this
   have B:a 2 M=0:=by have:=hd M d;simp[o] at this;exact this.resolve_left Y
   have p:b 2 M=a 0 M:=by have:=hs M d;simp[o] at this;linear_combination this/2
   have T:M=a 0 M•![u,u,v]:=funext λ i=>by
    rw[f M i];fin_cases i
    . simp[r,L]
    . simp[o,l M d,r,k M d,L]
    . simp[B,p,g M d,r]
   have⟨α,hα⟩:∃ α,a 0 M=α:=⟨_,rfl⟩;rw[hα] at T;have C:α≠0:=λ h0=>Z (by rw[T,h0,zero_smul]);exact QN h F (by have:=S.smul_mem α⁻¹ d;rwa[T,smul_smul,inv_mul_cancel₀ C,one_smul] at this)
lemma Zy (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (a:∀ x y z,H x y z=H y x z) (x y z:zu) (α π γ:KD):H (α•x-π•y) (π•x+α•y) (γ•z)=γ*((α^2-π^2)*H x y z+α*π*(H x x z-H y y z)):=by simp only[map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul];rw[a y x z];ring
lemma vn {E:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] (S:Submodule KD E) {A D:KD} (g:A≠0) (α π γ:E →ₗ[KD] KD) (b:∀ M∈S,(1+γ M)*(((1+α M)^2-π M^2)*A+(1+α M)*π M*D)=A) (h:∀ M∈S,π M=0->α M=0->γ M=0 -> M=0):finrank KD S≤1:=by
 have d:=kc (c:=1) S g γ _ b;have i:∀ M∈S,2*α M*A+π M*D=0:=λ M a=>by
  obtain⟨-,f,-⟩:=qc 0 (2*α M*A+π M*D) ((α M^2-π M^2)*A+α M*π M*D) λ t=>by have:=b _ (S.smul_mem t a);rw[d _ (S.smul_mem t a)] at this;simp only[map_smul,smul_eq_mul] at this;linear_combination this
  exact f
 refine kw S π λ M a e=>h M a e ?_ (d M a);grind
lemma xD (e c a b d:KD) (h:c≠0) (g:∀ t:KD,(e+t*b)^2*(c+t*d)^2+(t*a)^2*(c+t*d)^2+(t*a)^2*(e+t*b)^2=0) (f:e=0):a=0:=by
 subst f;obtain⟨-,-,i,-,j⟩:=qD 0 0 ((b^2+a^2)*c^2) (2*(b^2+a^2)*c*d) ((b^2+a^2)*d^2+a^2*b^2) λ t=>by linear_combination g t
 grind
open LinearMap in
lemma QP (q:zu →ₗ[KD] zu →ₗ[KD] KD) (a8:∀ x y,q x y=q y x) (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (s:∀ x y z,H x y z=H y x z) (W:∀ x y z,H x y z=H x z y) {f:Fin 3 -> zu} (hf:∀ i j,q (f i) (f j)=if i=j then 1 else 0) {S:Submodule KD (Fin 3 -> zu)} {A:KD} (Z:A≠0) (h:jJ q H f S A):finrank KD S≤1:=by
 have co:=x9 q f f hf;simp only[sum_univ_three] at co;set N:Fin 3 -> Fin 3->(Fin 3 -> zu) →ₗ[KD] KD:=λ i j=>jX q (f i) j;have o:∀ M j,M j=N 0 j M•f 0+N 1 j M•f 1+N 2 j M•f 2:=λ M j=>co (M j);have qe:∀ x y,q x y=q y (f 0)*q x (f 0)+q y (f 1)*q x (f 1)+q y (f 2)*q x (f 2):=λ x y=>by
  conv_lhs=>rw[co y]
  simp only[map_add,map_smul,smul_eq_mul]
 have K:∀ M∈S,∀ u v,u≠v -> N v u M = - N u v M:=λ M a u v L=>by have:=(kd h a L).2.1;rw[a8 (f u)] at this;simp only[N,vm];linear_combination this
 have Qd:∀ M∈S,∀ u v,u≠v -> N 0 v M*N 0 u M+N 1 v M*N 1 u M+N 2 v M*N 2 u M=0:=λ M a u v L=>by have:=(kd h a L).2.2;rw[qe] at this;exact this
 have O:H (f 0) (f 1) (f 2)=A:=by simpa using (h 0 S.zero_mem).2
 have hv:=λ M a=>(h M a).2;have P:=λ M a=>K M a 0 1 (by decide);have Q:=λ M a=>K M a 0 2 (by decide);have R:=λ M a=>K M a 1 2 (by decide);have E1:∀ M∈S,N 0 1 M*(N 0 0 M-N 1 1 M)+N 0 2 M*N 1 2 M=0:=by grind
 have E2:∀ M∈S,N 0 2 M*(N 0 0 M-N 2 2 M)-N 0 1 M*N 1 2 M=0:=by grind
 have E3:∀ M∈S,N 0 1 M*N 0 2 M+N 1 2 M*(N 1 1 M-N 2 2 M)=0:=by grind
 have z0:∀ M∈S,N 0 1 M=0 -> N 0 2 M=0 -> N 1 2 M=0 -> N 0 0 M=0 -> N 1 1 M=0 -> N 2 2 M=0 -> M=0:=λ M a p0 q0 r0 a0 b0 c0=>funext λ j=>by
  rw[o M j];fin_cases j
  . simp[a0,P M a,Q M a,p0,q0]
  . simp[p0,b0,R M a,r0]
  . simp[q0,r0,c0]
 have zl:(∀ M∈S,M=0) -> finrank KD S≤1:=λ hz=>kw S 0 λ M a _=>hz M a;have c0:∀ M∈S,f 0+M 0=(1+N 0 0 M)•f 0-N 0 1 M•f 1-N 0 2 M•f 2:=λ M a=>by rw[o M 0,P M a,Q M a];module
 have c1:∀ M∈S,f 1+M 1=N 0 1 M•f 0+(1+N 1 1 M)•f 1-N 1 2 M•f 2:=λ M a=>by rw[o M 1,R M a];module
 have c2:∀ M∈S,f 2+M 2=N 0 2 M•f 0+N 1 2 M•f 1+(1+N 2 2 M)•f 2:=λ M a=>by rw[o M 2];module
 have B:∀ M∈S,H ((1+N 0 0 M)•f 0-N 0 1 M•f 1-N 0 2 M•f 2) (N 0 1 M•f 0+(1+N 1 1 M)•f 1-N 1 2 M•f 2) (N 0 2 M•f 0+N 1 2 M•f 1+(1+N 2 2 M)•f 2)=A:=λ M a=>by grind
 have J:∀ g k:(Fin 3 -> zu) →ₗ[KD] KD,¬ (∀ M∈S,g M=0)->(∀ M∈S,g M*k M=0)->∀ M∈S,k M=0:=λ g k hg a4=>(zz S g k a4).resolve_left hg;have s1:H (f 1) (f 0) (f 2)=A:=by grind
 have s2:H (f 0) (f 2) (f 1)=A:=by grind
 have s3:H (f 1) (f 2) (f 0)=A:=by rw[←W,←s];exact O
 by_cases b:∀ M∈S,N 0 1 M=0<;>by_cases c:∀ M∈S,N 0 2 M=0<;>by_cases m:∀ M∈S,N 1 2 M=0
 . obtain⟨-,H3⟩:=Zx S Z (N 0 0) (N 1 1) (N 2 2) 0 (X:=A) (Y:=0) λ M a=>by
    have:=B M a;rw[b M a,c M a,m M a] at this;simp only[zero_smul,sub_zero,zero_add,add_zero,map_smul,LinearMap.smul_apply,smul_eq_mul,O] at this;grind
   grind
 . have a1:=J (N 1 2) (N 1 1-N 2 2) m λ M a=>by
    have:=E3 M a;rw[b M a] at this;simpa using this
   refine vn S Z (N 1 1) (N 1 2) (N 0 0) (D:=H (f 1) (f 1) (f 0)-H (f 2) (f 2) (f 0)) (λ M a=>?_) λ M a T p U=>z0 M a (b M a) (c M a) T U p ?_
   . have e:N 2 2 M=N 1 1 M:=by have:=a1 M a;simp at this;linear_combination -this
     have:=B M a;rw[b M a,c M a,e] at this;simp only[zero_smul,sub_zero,zero_add] at this;rw[s,W,Zy H s,s3] at this;linear_combination this
   . simpa[p] using a1 M a
 . have C:=J (N 0 2) (N 0 0-N 2 2) c λ M a=>by
    have:=E2 M a;rw[b M a] at this;simpa using this
   refine vn S Z (N 0 0) (N 0 2) (N 1 1) (D:=H (f 0) (f 0) (f 1)-H (f 2) (f 2) (f 1)) (λ M a=>?_) λ M a T p U=>z0 M a (b M a) T (m M a) p U ?_
   . have e:N 2 2 M=N 0 0 M:=by have:=C M a;simp at this;linear_combination -this
     have:=B M a;rw[b M a,m M a,e] at this;simp only[zero_smul,sub_zero,zero_add,add_zero] at this;rw[W,Zy H s,s2] at this;linear_combination this
   . simpa[p] using C M a
 . exact absurd (J (N 0 2) (N 1 2) c λ M a=>by have:=E1 M a;rw[b M a] at this;simpa using this) m
 . have E:=J (N 0 1) (N 0 0-N 1 1) b λ M a=>by
    have:=E1 M a;rw[c M a] at this;simpa using this
   refine vn S Z (N 0 0) (N 0 1) (N 2 2) (D:=H (f 0) (f 0) (f 2)-H (f 1) (f 1) (f 2)) (λ M a=>?_) λ M a T p U=>z0 M a T (c M a) (m M a) p ?_ U
   . have e:N 1 1 M=N 0 0 M:=by have:=E M a;simp at this;linear_combination -this
     have:=B M a;rw[c M a,m M a,e] at this;simp only[zero_smul,sub_zero,zero_add,add_zero] at this;rw[Zy H s,O] at this;linear_combination this
   . simpa[p] using E M a
 . exact absurd (J (N 0 1) (N 1 2) b λ M a=>by have:=E2 M a;rw[c M a] at this;simpa using this) m
 . exact absurd (J (N 0 1) (N 0 2) b λ M a=>by have:=E3 M a;rw[m M a] at this;simpa using this) c
 . have hF:∀ M∈S,N 0 2 M^2*N 1 2 M^2+N 0 1 M^2*N 1 2 M^2+N 0 1 M^2*N 0 2 M^2=0:=λ M a=>by
    grind
   push Not at b;have⟨d,F,V⟩:=b;have hl:∀ M∈S,N 0 1 M=0->∀ t:KD,(N 0 2 M+t*N 0 2 d)^2*(N 1 2 M+t*N 1 2 d)^2+(t*N 0 1 d)^2*(N 1 2 M+t*N 1 2 d)^2+(t*N 0 1 d)^2*(N 0 2 M+t*N 0 2 d)^2=0:=λ M a l t=>by have:=hF _ (S.add_mem a (S.smul_mem t F));simp only[map_add,map_smul,smul_eq_mul,l,zero_add] at this;exact this
   have kq:∀ M∈S,N 0 1 M=0 -> N 0 2 M=0/\N 1 2 M=0:=by
    rcases zz (S⊓ker (N 0 1)) (N 0 2) (N 1 2) λ M a=>by have:=hF M a.1;rw[mem_ker.1 a.2] at this;exact pow_eq_zero_iff (n:=2) (by norm_num) |>.1 (by linear_combination this) with a2|a3
    . refine λ M a l=>⟨a2 M ⟨a,l⟩,?_⟩
      by_contra a5;exact V (xD _ _ _ _ _ a5 (hl M a l) (a2 M ⟨a,l⟩))
    . refine λ M a l=>⟨?_,a3 M ⟨a,l⟩⟩
      by_contra a6;exact V (xD (N 1 2 M) (N 0 2 M) _ (N 1 2 d) (N 0 2 d) a6 (λ t=>by linear_combination hl M a l t) (a3 M ⟨a,l⟩))
   have a9:N 0 2 d≠0:=λ l=>c λ M a=>by have h1:=kq (M-(N 0 1 M/N 0 1 d)•d) (S.sub_mem a (S.smul_mem _ F)) (by simp[div_mul_cancel₀ _ V]);have:=h1.1;simp[l] at this;exact this
   by_contra b1;have⟨D,w,b2,r⟩:=wD (N 0 1) S (by have:=finrank_le (S.map (N 0 1));rw[finrank_self] at this;omega);have⟨G,I⟩:=kq D w r;have E:N 1 1 D=N 0 0 D:=by have:=E1 _ (S.add_mem F w);simp only[map_add,r,G,I] at this;grind
   have C:N 2 2 D=N 0 0 D:=by have:=E2 _ (S.add_mem F w);simp only[map_add,r,G,I] at this;grind
   have⟨α,hα⟩:∃ α,N 0 0 D=α:=⟨_,rfl⟩;have hB:D=α•f:=funext λ j=>by
    rw[o D j];fin_cases j
    . simp[hα,P D w,Q D w,r,G]
    . simp[r,E,hα,R D w,I]
    . simp[G,I,C,hα]
   have a7:α≠0:=by grind
   exact QN h Z (by have:=S.smul_mem α⁻¹ w;rwa[hB,smul_smul,inv_mul_cancel₀ a7,one_smul] at this)
open LinearMap in
lemma vo {q H B S A} (h:jJ q H B S A) (σ:Perm (Fin 3)) (c:∀ X:Fin 3 -> zu,H (X (σ 0)) (X (σ 1)) (X (σ 2))=H (X 0) (X 1) (X 2)):jJ q H (B∘σ) (S.map (funLeft KD zu σ)) A/\finrank KD (S.map (funLeft KD zu σ))=finrank KD S:=by refine⟨?_,(equivMapOfInjective _ (funLeft_injective_of_surjective _ _ _ σ.surjective) S).finrank_eq.symm⟩;rintro _ ⟨M,a,rfl⟩;refine⟨λ u v b=>(h M a).1 _ _ (σ.injective.ne b),?_⟩;exact(c (λ i=>B i+M i)).trans (h M a).2
open LinearMap in
lemma vp {q H B S A} (h:jJ q H B S A) (d:Fin 3->KD) (c:∀ i,d i≠0):jJ q H (λ i=>d i•B i) (S.map (LinearMap.pi λ i=>d i•proj i)) (d 0*d 1*d 2*A)/\finrank KD (S.map (LinearMap.pi λ i=>d i•proj i))=finrank KD S:=by
 refine⟨?_,(equivMapOfInjective _ (λ M f e=>funext λ i=>by have:=congrFun e i;simpa[c i] using this) S).finrank_eq.symm⟩;rintro _ ⟨M,a,rfl⟩;refine⟨λ u v b=>?_,?_⟩
 . have:=(h M a).1 u v b;simp only[pi_apply,LinearMap.smul_apply,proj_apply,←smul_add,map_smul,LinearMap.smul_apply,smul_eq_mul,this,mul_zero]
 . simp only[pi_apply,LinearMap.smul_apply,proj_apply,←smul_add,map_smul,LinearMap.smul_apply,smul_eq_mul,(h M a).2];ring
lemma xE (q:zu →ₗ[KD] zu →ₗ[KD] KD) (d:∀ x y,q x y=q y x) (p:∀ x,(∀ y,q x y=0) -> x=0) (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (r:∀ x y z,H x y z=H y x z) (s:∀ x y z,H x y z=H x z y) {B:Fin 3 -> zu} {S:Submodule KD (Fin 3 -> zu)} {A:KD} (C:A≠0) (h:jJ q H B S A) (D:B 0≠0) (e:q (B 0) (B 0)=0) {α:KD} (f:α≠0) (E:B 1=α•B 0) (F:q (B 2) (B 2)≠0):finrank KD S≤1:=by
 have⟨ρ,t⟩:=jj (q (B 2) (B 2));have a:ρ≠0:=by grind
 have g:q (B 0) (B 2)=0:=by simpa using (h 0 (Submodule.zero_mem _)).1 0 2 (by decide)
 set v:=ρ⁻¹•B 2;have b:q v v=1:=by simp only[v,map_smul,LinearMap.smul_apply,smul_eq_mul,←t];field_simp
 have c:q (B 0) v=0:=by simp[v,g]
 have⟨w,j,k,l⟩:=QM q d p D e b c;have⟨m,u⟩:=vp h ![1,α⁻¹,ρ⁻¹] (λ i=>by fin_cases i<;>simp[f,a]);have n:![1,α⁻¹,ρ⁻¹] 0*![1,α⁻¹,ρ⁻¹] 1*![1,α⁻¹,ρ⁻¹] 2*A≠0:=by simp[f,a,C]
 have o:(λ i=>![1,α⁻¹,ρ⁻¹] i•B i)=![B 0,B 0,v]:=by funext i;fin_cases i<;>simp[E,smul_smul,inv_mul_cancel₀ f,v]
 rw[o] at m;exact u ▸ WZ q d H r s e j k b c l n m
lemma QR (q:zu →ₗ[KD] zu →ₗ[KD] KD) (a:∀ x y,q x y=q y x) (s:∀ x,(∀ y,q x y=0) -> x=0) (H:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD) (t:∀ x y z,H x y z=H y x z) (C:∀ x y z,H x y z=H x z y) {B:Fin 3 -> zu} {S:Submodule KD (Fin 3 -> zu)} {A:KD} (I:A≠0) (h:jJ q H B S A):finrank KD S≤1:=by
 have n:∀ {B:Fin 3 -> zu} {S:Submodule KD (Fin 3 -> zu)},jJ q H B S A->∀ i,B i≠0:=λ {B S} h i e=>I (by
  have:=(h 0 S.zero_mem).2;simp only[Pi.zero_apply,add_zero] at this;rw[←this];fin_cases i
  . rw[show B 0=0 from e];simp
  . rw[show B 1=0 from e];simp
  . rw[show B 2=0 from e];simp)
 have E:∀ {B:Fin 3 -> zu} {S:Submodule KD (Fin 3 -> zu)},jJ q H B S A->∀ u v,u≠v -> q (B u) (B v)=0:=λ {B S} h u v b=>by simpa using (h 0 S.zero_mem).1 u v b
 have V:∀ X:Fin 3 -> zu,H (X (swap 0 1 0)) (X (swap 0 1 1)) (X (swap 0 1 2))=H (X 0) (X 1) (X 2):=λ X=>by grind
 have W:∀ X:Fin 3 -> zu,H (X (swap 0 2 0)) (X (swap 0 2 1)) (X (swap 0 2 2))=H (X 0) (X 1) (X 2):=λ X=>by grind
 have Y:∀ X:Fin 3 -> zu,H (X (swap 1 2 0)) (X (swap 1 2 1)) (X (swap 1 2 2))=H (X 0) (X 1) (X 2):=λ X=>by grind
 have Q:∀ {B:Fin 3 -> zu} {S:Submodule KD (Fin 3 -> zu)},jJ q H B S A -> q (B 0) (B 0)=0 -> finrank KD S≤1:=λ {B S} h c=>by
  have e:=n h 0;have⟨v,o,b⟩:=WV q a s e;have⟨w,L,M,N⟩:=QM q a s e c o b;have Z:=x9 q ![B 0,v,w] ![w,v,B 0] (λ i j=>by fin_cases i<;>fin_cases j<;>simp[c,L,M,o,b,N,a w (B 0),a v (B 0),a w v]);simp[sum_univ_three] at Z;have J:∀ k,k≠0 -> B k=q (B k) w•B 0+q (B k) v•v:=λ k R=>by have:=Z (B k);rw[a (B k) (B 0),E h 0 k R.symm,zero_smul,add_zero] at this;exact this
  have T:∀ k l,k≠0 -> l≠0 -> q (B k) (B l)=q (B k) v*q (B l) v:=λ k l R hl=>by rw[J k R,J l hl];simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,c,b,o,a v (B 0)];ring
  have O:=E h 1 2 (by decide);rw[T 1 2 (by decide) (by decide)] at O;by_cases p:q (B 1) v=0
  . have K:B 1=q (B 1) w•B 0:=by
     have:=J 1 (by decide);rw[p,zero_smul,add_zero] at this;exact this
    have f:q (B 1) w≠0:=λ F=>n h 1 (by rw[K,F,zero_smul]);by_cases r:q (B 2) v=0
    . have D:B 2=q (B 2) w•B 0:=by
       grind
      have d:q (B 2) w≠0:=λ F=>n h 2 (by rw[D,F,zero_smul]);generalize q (B 1) w=α1 at K f;generalize q (B 2) w=α2 at D d;have⟨g,m⟩:=vp h ![1,α1⁻¹,α2⁻¹] (λ i=>by fin_cases i<;>simp[f,d]);have a0:(λ i=>![1,α1⁻¹,α2⁻¹] i•B i)=λ _=>B 0:=by
       funext i;fin_cases i
       . simp
       . simp[K,smul_smul,inv_mul_cancel₀ f]
       . simp[D,smul_smul,inv_mul_cancel₀ d]
      rw[a0] at g;exact m ▸ WX q a H t C c L M o b N (by simp[f,d,I]) g
    . exact xE q a s H t C I h e c f K (by rw[T 2 2 (by decide) (by decide)];exact mul_ne_zero r r)
  . have r:q (B 2) v=0:=(mul_eq_zero.1 O).resolve_left p
    have D:B 2=q (B 2) w•B 0:=by have:=J 2 (by decide);rw[r,zero_smul,add_zero] at this;exact this
    have d:q (B 2) w≠0:=λ F=>n h 2 (by rw[D,F,zero_smul]);have⟨g,m⟩:=vo h (swap 1 2) Y;rw[←m];have U:swap (1:Fin 3) 2 0=0:=by decide
    have w1:swap (1:Fin 3) 2 1=2:=by decide
    have w2:swap (1:Fin 3) 2 2=1:=by decide
    exact xE q a s H t C I g (by simpa[U] using e) (by simpa[U] using c) d (by simpa[U,w1] using D) (by simp only[Function.comp_apply,w2];rw[T 1 1 (by decide) (by decide)];exact mul_ne_zero p p)
 by_cases h3:∀ i,q (B i) (B i)≠0
 . choose ρ hρ using λ i=>jj (q (B i) (B i))
   have G:∀ i,ρ i≠0:=by grind
   have⟨g,m⟩:=vp h (λ i=>(ρ i)⁻¹) (λ i=>inv_ne_zero (G i));rw[←m];refine QP q a H t C (λ i j=>?_) (by simp[G,I]) g;simp only[map_smul,LinearMap.smul_apply,smul_eq_mul];split_ifs with P
   . subst P;rw[←hρ i];have:=G i;field_simp
   . rw[E h i j P];ring
 . push Not at h3;have⟨i,hi⟩:=h3
   fin_cases i
   . exact Q h hi
   . have⟨g,m⟩:=vo h (swap 0 1) V;grind
   . have⟨g,m⟩:=vo h (swap 0 2) W;grind
def yH (z:Fin 3->KD):zu →ₗ[KD] zu →ₗ[KD] KD :=
 LinearMap.mk₂ KD (λ x y=>z 2*(x 0*y 1+x 1*y 0)+z 1*(x 0*y 2+x 2*y 0) +
  z 0*(x 1*y 2+x 2*y 1)) (by intros;simp;ring) (by intros;simp;ring)
  (by intros;simp;ring) (by intros;simp;ring)
def kI:zu →ₗ[KD] zu →ₗ[KD] zu →ₗ[KD] KD where
 toFun x:=LinearMap.mk₂ KD (λ y w=>x 0*(y 1*w 2+y 2*w 1)+x 1*(y 0*w 2+y 2*w 0) +
  x 2*(y 0*w 1+y 1*w 0)) (by intros;simp;ring) (by intros;simp;ring)
  (by intros;simp;ring) (by intros;simp;ring)
 map_add' x x':=LinearMap.ext λ y=>LinearMap.ext λ w=>by simp;ring
 map_smul' c x:=LinearMap.ext λ y=>LinearMap.ext λ w=>by simp;ring
open LinearMap in
lemma QS (B:zx) (N:Submodule KD zx) (z:Fin 3->KD) (s:z 0*z 1*z 2≠0) {q:KD} (t:q≠0) (A:∀ S∈N,zo (B+S)=q) (D:∀ S∈N,∀ k,∑ a,z a*zn (B+S) a k=0):finrank KD N≤1:=by
 let T:zx →ₗ[KD] (Fin 3 -> zu):=LinearMap.pi λ k=>LinearMap.pi λ a=>(proj k:(Fin 3->KD) →ₗ[KD] KD).comp (proj a:zx →ₗ[KD] Fin 3->KD);have r:Function.Injective T:=λ C E e=>funext λ a=>funext λ k=>by have:=congrFun (congrFun e k) a;simpa[T] using this
 rw[(equivMapOfInjective T r N).finrank_eq];have f:∀ x y,yH z x y=yH z y x:=λ x y=>by simp[yH];ring
 have h:∀ C:zx,∀ k,∑ a,z a*zn C a k=yH z (T C (z6 k 0)) (T C (z6 k 1)):=λ C k=>by fin_cases k<;>simp[zK,z6,yH,sum_univ_three,T]<;>ring
 refine QR (yH z) f (λ x g=>?_) kI (λ x y w=>by simp[kI];ring) (λ x y w=>by simp[kI];ring) (B:=T B) t ?_
 . have b:=g (Pi.single 0 1);have c:=g (Pi.single 1 1);have d:=g (Pi.single 2 1)
   simp[yH] at b c d;have⟨j,l⟩:=mul_ne_zero_iff.1 s;have⟨m,n⟩:=mul_ne_zero_iff.1 j;funext i;fin_cases i
   . have:2*z 1*z 2*x 0=0:=by linear_combination z 2*d+z 1*c-z 0*b
     simpa[n,l] using this
   . have:2*z 0*z 2*x 1=0:=by linear_combination z 2*d+z 0*b-z 1*c
     simpa[m,l] using this
   . have:2*z 0*z 1*x 2=0:=by linear_combination z 1*c-z 2*d+z 0*b
     simpa[m,n] using this
 . rintro _ ⟨S,o,rfl⟩
   refine⟨λ u v p=>?_,?_⟩
   . have e:∀ k,yH z (T (B+S) (z6 k 0)) (T (B+S) (z6 k 1))=0:=λ k=>(h _ k).symm.trans (D S o k)
     obtain⟨k,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩:=w5 u v p
     . simpa[map_add] using e k
     . rw[f];simpa[map_add] using e k
   . rw[←A S o];simp[kI,T,zs];ring
def y7:ze:=λ p=>if p=(1,0) then (1:KD) else if p=(2,0) then -1 else 0
lemma QT (C:zx) (h:∀ k,zn C 0 k=zn C 1 k):(C 0 0-C 1 0)*(C 0 1-C 1 1)*(C 0 2-C 1 2)*zo C=0:=by have a:=h 0;have b:=h 1;have c:=h 2;simp only[zK,z6,cons_val_zero,cons_val_one,head_cons,cons_val_two,Matrix.tail_cons] at a b c;rw[zs];grind
lemma QU (C:zx) (c:Fin 3) (a:C 2 c=0) (b:C 2 (z6 c 1)=C 2 (z6 c 0)) (d:C 1 c=C 0 c) (e:C 1 (z6 c 1)=C 0 (z6 c 1)+C 0 (z6 c 0)-C 1 (z6 c 0)):zo C=2*C 2 (z6 c 0)*C 0 c*(C 0 (z6 c 0)+C 0 (z6 c 1)):=by rw[zs];fin_cases c<;>simp only[z6] at a b d e⊢<;>simp at a b d e⊢<;>grind
lemma xF (C:zx) (k:Fin 3):zn C 0 k-zn C 1 k = -((C 0 (z6 k 0)-C 1 (z6 k 0))*C 2 (z6 k 1)+(C 0 (z6 k 1)-C 1 (z6 k 1))*C 2 (z6 k 0)):=by fin_cases k<;>simp[zK,z6]<;>ring
def yX (X:ze) (c:Fin 4):KD:=X (1,c)-X (2,c)
lemma w8 (hL:zg L) (hA:y7∈L) {X:ze} (hX:X∈zP L):yX X 1+yX X 2+yX X 3=0/\yX X 1*(X (0,1)+X (3,1))+yX X 2*(X (0,2)+X (3,2))+yX X 3*(X (0,3)+X (3,3))=0/\zo ![![X (0,1),X (0,2),X (0,3)],![yX X 1,yX X 2,yX X 3],![X (3,1),X (3,2),X (3,3)]]=0:=by
 have F:∀ c:KD,wM (X+c•qk) 1 0-wM (X+c•qk) 2 0=0:=λ c=>by have:=QI hL ((zP L).add_mem hX ((zP L).smul_mem c (mem_sup_right (mem_span_singleton_self _)))) hA (λ a b g=>by simp[y7,g]);simp[y7,sum_univ_four] at this;linear_combination this
 have d:=F 0;have e:=F 1;have f:=F (-1);simp only[wM,zs,z8,qk,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at d e f;simp at d e f;simp only[yX,zs];simp;grind
open LinearMap in
lemma QV (v:zg L) (c:Fin 3) (p:∀ S∈zh L 0,(∀ b,S (3,z8 0 b)=0)/\S (1,z8 0 c)=0/\S (2,z8 0 c)=0/\S (1,z8 0 (z6 c 1)) = -S (1,z8 0 (z6 c 0))/\S (2,z8 0 (z6 c 1)) = -S (2,z8 0 (z6 c 0))):finrank KD ((zh L 0).map (z7 0 0))≤1:=by
 set K:=zh L 0;have t:∀ S∈K,S (1,z8 0 (z6 c 0))*S (2,z8 0 (z6 c 0))=0:=λ S d=>by have⟨m,f⟩:=(qb v d.1).imp_right And.left;have u:∀ j,S (0,j)=0:=λ j=>congrFun (mem_ker.1 d.2) j;have⟨w,g,h,k,l⟩:=p S d;have q:=w 0;have r:=w 1;have s:=w 2;simp only[qY,yl,Fintype.sum_prod_type,sum_univ_four,u] at m f;fin_cases c<;>simp[z8,z6] at q r s g h k l m f<;>simp only[q,r,s,g,h,k,l] at m f<;>dsimp only[z8,z6]<;>simp only[zero_eta,mk_one,reduceFinMk,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons]<;>linear_combination (-1/4:KD)*f
 rcases zz K (proj (1,z8 0 (z6 c 0))) (proj (2,z8 0 (z6 c 0))) t with m|f
 . refine kw _ ((proj (z6 c 0):(Fin 3->KD) →ₗ[KD] KD).comp (proj 1:zx →ₗ[KD] Fin 3->KD)) ?_
   rintro _ ⟨S,d,rfl⟩ e;have⟨w,g,h,k,l⟩:=p S d;have n:S (1,z8 0 (z6 c 0))=0:=m S d;have o:S (2,z8 0 (z6 c 0))=0:=e;funext a b;simp only[zt,Pi.zero_apply];rcases wE c b with rfl|⟨i,rfl⟩<;>fin_cases a
   . exact g
   . exact h
   . exact w _
   all_goals fin_cases i
   exacts[n,k.trans (by rw[n,neg_zero]),o,l.trans (by rw[o,neg_zero]),w _,w _]
 . refine kw _ ((proj (z6 c 0):(Fin 3->KD) →ₗ[KD] KD).comp (proj 0:zx →ₗ[KD] Fin 3->KD)) ?_
   rintro _ ⟨S,d,rfl⟩ e;have⟨w,g,h,k,l⟩:=p S d;have n:S (1,z8 0 (z6 c 0))=0:=e;have o:S (2,z8 0 (z6 c 0))=0:=f S d;funext a b;simp only[zt,Pi.zero_apply];rcases wE c b with rfl|⟨i,rfl⟩<;>fin_cases a
   . exact g
   . exact h
   . exact w _
   all_goals fin_cases i
   exacts[n,k.trans (by rw[n,neg_zero]),o,l.trans (by rw[o,neg_zero]),w _,w _]
open LinearMap in
lemma QW (U:Submodule KD (Fin 3->KD)) (h:∀ x∈U,x 0*x 1+x 0*x 2+x 1*x 2=0):finrank KD U≤1:=by
 let B:(Fin 3->KD) →ₗ[KD] (Fin 3->KD) →ₗ[KD] KD:=mk₂ KD (λ x y=>x 0*(y 1+y 2)+x 1*(y 0+y 2)+x 2*(y 0+y 1)) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring);have b:∀ x y,B x y=B y x:=λ x y=>by simp[B];ring
 have c:=yr B b U λ x a=>by simp[B];linear_combination 2*h x a
 have d:U⊓ker B=⊥:=(Submodule.eq_bot_iff _).2 λ x a=>by
  have e:=λ y=>LinearMap.congr_fun (mem_ker.1 (Submodule.mem_inf.1 a).2) y;have f:=e (Pi.single 0 1);have g:=e (Pi.single 1 1);have j:=e (Pi.single 2 1);simp[B] at f g j;have k:x 0=0:=by grind
  have l:x 1=0:=by grind
  have m:x 2=0:=by grind
  funext i;fin_cases i;exacts[k,l,m]
 have:=qr B U U c;rw[d,finrank_bot] at this;simp at this;omega
lemma xG:∀ c:Fin 3,(z6 (z6 c 1) 0=c/\z6 (z6 c 1) 1=z6 c 0)\/(z6 (z6 c 1) 0=z6 c 0/\z6 (z6 c 1) 1=c):=by decide
lemma jk:∀ c b:Fin 3,b=c\/b=z6 c 0\/b=z6 c 1:=by decide
lemma QX (C:zx) (c:C 1=C 0) (a:∀ b,C 2 b=C 2 0):zo C=2*C 2 0*(C 0 0*C 0 1+C 0 0*C 0 2+C 0 1*C 0 2):=by rw[zs,c,a 1,a 2];ring
lemma QY (j:Fin 3) (g w:Fin 3->KD):zo ![Pi.single j 1,g,w]=g (z6 j 0)*w (z6 j 1)+g (z6 j 1)*w (z6 j 0):=by fin_cases j<;>simp[zs,z6]
lemma QZ (a c G w:Fin 3->KD) (t φ:KD):zo ![λ b=>a b+t*c b,λ b=>(1+t*φ)*G b,w]=(1+t*φ)*(zo ![a,G,w]+t*zo ![c,G,w]):=by simp[zs];ring
lemma xH {E:Type} [AddCommGroup E] [Module KD E] (K:Submodule KD E) (c d:KD) (φ ψ:E →ₗ[KD] KD) (h:∀ S∈K,(c+φ S)*(d+ψ S)=0):(c=0/\∀ S∈K,φ S=0)\/(d=0/\∀ S∈K,ψ S=0):=by
 have⟨i,b,e⟩:=yS K ![c,d] ![φ,ψ] λ S a=>by simpa[prod_univ_two] using h S a
 fin_cases i<;>simp_all
open LinearMap in
lemma xI (y:zg L) {h:ze} {l:KD} (j:l≠0) (z:∀ S∈zh L 0,zo (z7 0 0 (h+S))=l) (E:2≤finrank KD ((zh L 0).map (z7 0 0))) (c:Fin 3) (m:∀ S∈zh L 0,z7 0 0 (h+S) 2 c=0/\z7 0 0 (h+S) 2 (z6 c 1)=z7 0 0 (h+S) 2 (z6 c 0)/\z7 0 0 (h+S) 1 c=z7 0 0 (h+S) 0 c/\z7 0 0 (h+S) 1 (z6 c 1)=z7 0 0 (h+S) 0 (z6 c 1)+z7 0 0 (h+S) 0 (z6 c 0)-z7 0 0 (h+S) 1 (z6 c 0)):False:=by
 set K:=zh L 0;set C:ze -> zx:=λ S=>z7 0 0 (h+S);set g:Fin 3 -> Fin 3 -> ze →ₗ[KD] KD:=λ r b=>proj (z8 0 r,z8 0 b);have n:∀ S r b,C S r b=g r b h+g r b S:=λ S r b=>rfl;set u:=z6 c 0;set v:=z6 c 1;have e:∀ S∈K,2*C S 2 u*C S 0 c*(C S 0 u+C S 0 v)=l:=λ S i=>by have⟨a,b,d,f⟩:=m S i;rw[←z S i,QU (C S) c a b d f]
 have o:=kc (c:=g 2 u h) K j (g 2 u) (λ S=>2*C S 0 c*(C S 0 u+C S 0 v)) λ S i=>by grind
 have s:=kc (c:=g 0 c h) K j (g 0 c) (λ S=>2*C S 2 u*(C S 0 u+C S 0 v)) λ S i=>by grind
 have t:=kc (c:=(g 0 u+g 0 v) h) K j (g 0 u+g 0 v) (λ S=>2*C S 2 u*C S 0 c) λ S i=>by rw[←e S i,n S 0 u,n S 0 v,LinearMap.add_apply,LinearMap.add_apply];ring
 have p:∀ S∈K,g 2 c S=0/\g 2 v S=g 2 u S/\g 1 c S=g 0 c S/\g 1 v S=g 0 v S+g 0 u S-g 1 u S:=λ S i=>by have⟨a,b,d,f⟩:=m S i;have⟨A,k,B,D⟩:=m 0 K.zero_mem;grind
 refine(by omega:¬ finrank KD (K.map (z7 0 0))≤1) (QV y c λ S i=>?_);have⟨a,b,d,f⟩:=p S i;have w:∀ k,S (3,z8 0 k)=0:=λ k=>by
  rcases jk c k with rfl|rfl|rfl
  exacts[a,o S i,b.trans (o S i)]
 have q:=t S i;have x:=s S i;simp only[LinearMap.add_apply,g,proj_apply,show z8 0 0=1 from rfl,show z8 0 1=2 from rfl] at q f d x⊢;grind
lemma P2 (H:zg L) {f:ze} {B:KD} (m:B≠0) (D:∀ S∈zh L 0,zo (z7 0 0 (f+S))=B) (I:2≤finrank KD ((zh L 0).map (z7 0 0))) (o:∀ S∈zh L 0,∀ k,zn (z7 0 0 (f+S)) 0 k=zn (z7 0 0 (f+S)) 1 k) (J:∀ S∈zh L 0,∑ b,(z7 0 0 (f+S) 0 b-z7 0 0 (f+S) 1 b)=0) (E:¬ ∀ S∈zh L 0,∀ b,z7 0 0 (f+S) 0 b=z7 0 0 (f+S) 1 b):False:=by
 set K:=zh L 0;set C:ze -> zx:=λ S=>qZ (f+S);set a:Fin 3 -> Fin 3 -> ze →ₗ[KD] KD:=λ r b=>LinearMap.proj (z8 0 r,z8 0 b);have j:∀ S r b,C S r b=a r b f+a r b S:=λ S r b=>rfl;push Not at E;have⟨n,p,F,q⟩:=E;set g:Fin 3 -> ze →ₗ[KD] KD:=λ b=>a 0 b-a 1 b;have i:∀ S b,C S 0 b-C S 1 b=g b f+g b S:=λ S b=>by simp only[j,g,LinearMap.sub_apply];ring
 have⟨c,M,N⟩:=yS K (λ b=>g b f) g λ S d=>by have:=QT (C S) (o S d);rw[D S d] at this;rw[prod_univ_three,←i,←i,←i];exact(mul_eq_zero.1 this).resolve_right m
 have l:∀ S∈K,C S 0 c-C S 1 c=0:=λ S d=>by grind
 set u:=zV c 0;set v:=zV c 1;have s:∀ S∈K,C S 0 v-C S 1 v = -(C S 0 u-C S 1 u):=λ S d=>by have:=J S d;rw[qU _ c,l S d] at this;linear_combination this
 have t:¬ (g u f=0/\∀ S∈K,g u S=0):=λ ⟨O,P⟩=>q (by
  have G:C n 0 u-C n 1 u=0:=by grind
  obtain h|h|h:=jk c F<;>rw[h]
  . exact sub_eq_zero.1 (l n p)
  . exact sub_eq_zero.1 G
  . exact sub_eq_zero.1 (by grind))
 have w:=(xH K _ _ (g u) (a 2 c) λ S d=>by rw[←i,←j];have:=xF (C S) v;rcases xG c with⟨x,y⟩|⟨x,y⟩<;>rw[x,y] at this<;>linear_combination this-o S d v-C S 2 u*l S d).resolve_left t;have z:=(xH K (g u f) ((a 2 v-a 2 u) f) (g u) (a 2 v-a 2 u) λ S d=>by rw[←i,show(a 2 v-a 2 u) f+(a 2 v-a 2 u) S=C S 2 v-C S 2 u by simp only[LinearMap.sub_apply,j];ring];have:=xF (C S) c;linear_combination this-o S d c-C S 2 u*s S d).resolve_left t;refine xI H m D I c λ S d=>⟨?_,?_,?_,?_⟩
 . show C S 2 c=0;rw[j,w.1,w.2 S d,add_zero]
 . show C S 2 v=C S 2 u;have e:=z.2 S d;have A:=z.1;simp only[LinearMap.sub_apply] at e A;rw[j,j];linear_combination e+A
 . show C S 1 c=C S 0 c;linear_combination -l S d
 grind
lemma P3 (r:zg L) (s:y7∈L) {a:ze} (t:a∈zP L) (u:∀ j,a (0,j)=if j=0 then 1 else 0) (w:∀ S∈zh L 0,∀ b,z7 0 0 (a+S) 0 b=z7 0 0 (a+S) 1 b) {X:ze} (v:X∈zP L) {S:ze} (o:S∈zh L 0):(∑ b,(X (1,z8 0 b)-X (2,z8 0 b))*z7 0 0 (a+S) 2 b=0)/\zo ![λ b=>X (0,z8 0 b),λ b=>X (1,z8 0 b)-X (2,z8 0 b),z7 0 0 (a+S) 2]=0:=by
 have p:∀ j,S (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 o.2) j;obtain⟨-,d,c⟩:=w8 r s ((zP L).add_mem v ((zP L).add_mem t (mem_sup_left o.1)));obtain⟨-,q,e⟩:=w8 r s v;have f:∀ b,(a+S) (0,z8 0 b)=0:=λ b=>by simp[u,p,show z8 0 b≠0 by fin_cases b<;>decide]
 have g:∀ b,(a+S) (2,z8 0 b)=(a+S) (1,z8 0 b):=λ b=>(w S o b).symm;have h:=f 0;have i:=f 1;have k:=f 2;have l:=g 0;have m:=g 1;have n:=g 2;simp only[z8,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons] at h i k l m n;simp only[yX,Pi.add_apply] at d c q e;simp only[Pi.add_apply] at h i k l m n;simp only[zt,sum_univ_three,z8,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons,Pi.add_apply];rw[h,i,k,l,m,n] at d c;simp only[zs,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons,zt,z8,Pi.add_apply] at c e⊢;exact⟨by linear_combination d-q,by linear_combination c-e⟩
open LinearMap in
lemma P5 {e:ze} {p:KD} (i:p≠0) (O:∀ S∈zh L 0,zo (z7 0 0 (e+S))=p) (T:2≤finrank KD ((zh L 0).map (z7 0 0))) (q:∀ S∈zh L 0,∀ b,z7 0 0 (e+S) 0 b=z7 0 0 (e+S) 1 b) (G:Fin 3 -> Fin 3->KD) (w:∀ k,∀ S∈zh L 0,∑ b,G k b*z7 0 0 (e+S) 2 b=0) (y:∀ k,∑ b,G k b=0) {k l:Fin 3} (P:G k 0*G l 1-G k 1*G l 0≠0):False:=by
 set K:=zh L 0;set C:ze -> zx:=λ S=>z7 0 0 (e+S);have j:∀ S∈K,∀ b,C S 2 b=C S 2 0:=λ S d=>by
  have m:=w k S d;have n:=w l S d;have z:=y k;have A:=y l;simp only[sum_univ_three] at m n z A;have B:C S 2 0-C S 2 2=0:=by grind
  have D:C S 2 1-C S 2 2=0:=by grind
  intro b;fin_cases b
  . rfl
  . show C S 2 1=C S 2 0;linear_combination D-B
  grind
 have g:∀ S∈K,C S 2 0*(2*(C S 0 0*C S 0 1+C S 0 0*C S 0 2+C S 0 1*C S 0 2))=p:=λ S d=>by rw[←O S d,QX (C S) (funext λ b=>(q S d b).symm) (j S d)];ring
 have E:=kc (c:=e (3,1)) K i (proj (3,1)) _ g;have h:∀ S∈K,C S 2 0=C 0 2 0:=λ S d=>by show(e+S) (3,1)=(e+0) (3,1);simp[show S (3,1)=0 from E S d]
 have Q:C 0 2 0≠0:=λ f=>i (by have:=g 0 K.zero_mem;rw[f] at this;simp at this;exact this.symm);have F:∀ S∈K,C S 0 0*C S 0 1+C S 0 0*C S 0 2+C S 0 1*C S 0 2=C 0 0 0*C 0 0 1+C 0 0 0*C 0 0 2+C 0 0 1*C 0 0 2:=λ S d=>by have a:=g S d;have b:=g 0 K.zero_mem;rw[h S d] at a;grind
 have H:∀ S∈K,∀ t:KD,∀ r b,C (t•S) r b=C 0 r b+t*z7 0 0 S r b:=λ S d t r b=>by simp[C,zt]
 set π:zx →ₗ[KD] Fin 3->KD:=proj 0;have R:=QW ((K.map (z7 0 0)).map π) λ x o=>by
  obtain⟨_,⟨S,d,rfl⟩,rfl⟩:=o;obtain⟨-,-,I⟩:=qc 0 (C 0 0 0*(z7 0 0 S 0 1+z7 0 0 S 0 2)+C 0 0 1*(z7 0 0 S 0 0+z7 0 0 S 0 2)+C 0 0 2*(z7 0 0 S 0 0+z7 0 0 S 0 1)) (z7 0 0 S 0 0*z7 0 0 S 0 1+z7 0 0 S 0 0*z7 0 0 S 0 2+z7 0 0 S 0 1*z7 0 0 S 0 2) λ t=>by have:=F _ (K.smul_mem t d);simp only[H S d] at this;linear_combination this
  exact I
 have J:(K.map (z7 0 0))⊓ker π=⊥:=(Submodule.eq_bot_iff _).2 λ x o=>by
  obtain⟨⟨S,d,rfl⟩,f⟩:=o;have f:=mem_ker.1 f;funext r b;have m:z7 0 0 S 1 b=z7 0 0 S 0 b:=by have s:=q S d b;have u:=q 0 K.zero_mem b;simp only[zt,Pi.add_apply,add_zero] at s u⊢;linear_combination u-s
  have n:z7 0 0 S 2 b=0:=by have M:=j S d b;have N:=j 0 K.zero_mem b;have c:=h S d;simp only[C,zt,Pi.add_apply,Pi.zero_apply,add_zero] at M N c⊢;grind
  have v:z7 0 0 S 0 b=0:=congrFun f b;fin_cases r;exacts[v,m.trans v,n]
 have:=zW π (K.map (z7 0 0));rw[J,finrank_bot] at this;omega
lemma P6 (Q:zg L) {d:ze} {B:KD} (p:B≠0) (C:∀ S∈zh L 0,zo (z7 0 0 (d+S))=B) (R:2≤finrank KD ((zh L 0).map (z7 0 0))) (T:∀ S∈zh L 0,∀ b,z7 0 0 (d+S) 0 b=z7 0 0 (d+S) 1 b) (G:Fin 3 -> Fin 3->KD) (v:∀ k,∑ b,G k b=0) (U:∀ k j,∀ t:KD,∀ S∈zh L 0,zo ![λ b=>(if b=k then (1:KD) else 0)+t*(if b=j then 1 else 0),λ b=>G k b+t*G j b,z7 0 0 (d+S) 2]=0) {f x:Fin 3} (q:G f x≠0) (V:∀ k l,G k 0*G l 1-G k 1*G l 0=0):False:=by
 set K:=zh L 0;set g:=G f;have D:g 2 = -g 0-g 1:=by have:=v f;simp[sum_univ_three] at this;simp only[g];linear_combination this
 have r:∀ j,∃ φ,∀ b,G j b=φ*g b:=λ j=>by
  have W:G j 2 = -G j 0-G j 1:=by have:=v j;simp[sum_univ_three] at this;linear_combination this
  have h:=V f j;by_cases m:g 0=0
  . have n:g 1≠0:=λ n=>q (by fin_cases x<;>simp[g,m,n,D] at *)
    refine⟨G j 1/g 1,λ b=>?_⟩;have E:G j 0=0:=by grind
    fin_cases b<;>grind
  . refine⟨G j 0/g 0,λ b=>?_⟩;fin_cases b<;>grind
 have P:∀ j,∀ S∈K,zo ![Pi.single j 1,g,z7 0 0 (d+S) 2]=0:=λ j S a=>by
  have⟨φ,F⟩:=r j;obtain⟨X,Y,-⟩:=qc (zo ![Pi.single f 1,g,z7 0 0 (d+S) 2]) (φ*zo ![Pi.single f 1,g,z7 0 0 (d+S) 2]+zo ![Pi.single j 1,g,z7 0 0 (d+S) 2]) (φ*zo ![Pi.single j 1,g,z7 0 0 (d+S) 2]) λ t=>by have e:=U f j t S a;rw[show(λ b=>G f b+t*G j b)=λ b=>(1+t*φ)*g b from funext λ b=>by rw[F b];ring,show(λ b=>(if b=f then (1:KD) else 0)+t*(if b=j then 1 else 0))=λ b=>(Pi.single f (1:KD):Fin 3->KD) b+t*(Pi.single j (1:KD):Fin 3->KD) b from funext λ b=>by simp[Pi.single_apply],QZ] at e;linear_combination e
  grind
 set w:ze -> Fin 3->KD:=λ S=>z7 0 0 (d+S) 2;have o:∀ j,∀ S∈K,g (z6 j 0)*w S (z6 j 1)+g (z6 j 1)*w S (z6 j 0)=0:=λ j S a=>(QY j g _).symm.trans (P j S a);by_cases i:∀ b,g b≠0
 . have m:=o 0;have n:=o 1;have y:=o 2
   simp only[z6,cons_val_zero,cons_val_one,head_cons,cons_val_two,Matrix.tail_cons] at m n y;have H:∀ S∈K,w S=0:=λ S a=>by
    have E:=m S a;have s:=n S a;have u:=y S a;have I:2*g 1*g 2*w S 0=0:=by grind
    have J:2*g 0*g 2*w S 1=0:=by grind
    have M:2*g 0*g 1*w S 2=0:=by grind
    funext b;fin_cases b
    . simpa[i 1,i 2] using I
    . simpa[i 0,i 2] using J
    . simpa[i 0,i 1] using M
   have:=C 0 K.zero_mem;rw[add_zero] at this;have z:∀ b,z7 0 0 d 2 b=0:=λ b=>by simpa[w] using congrFun (H 0 K.zero_mem) b
   rw[zs,z 0,z 1,z 2] at this;simp at this;exact p this.symm
 push Not at i;have⟨c,A⟩:=i;have N:=v f;rw[qU _ c] at N;have O:g (z6 c 0)≠0:=λ m=>q (by
  have e:g (z6 c 1)=0:=by grind
  obtain h|h|h:=jk c x<;>rw[h]
  exacts[A,m,e])
 refine xI Q p C R c λ S a=>⟨?_,?_,?_,?_⟩
 . have e:=o (z6 c 1) S a
   rcases xG c with⟨s,u⟩|⟨s,u⟩<;>rw[s,u,A] at e<;>simp only[w] at e
   . exact(mul_eq_zero.1 (by linear_combination e)).resolve_left O
   grind
 . have e:=o c S a;simp only[w] at e;grind
 . exact(T S a c).symm
 grind
lemma P7 (i:zg L) (q:finrank KD L=6) (r:y7∈L) {M:Fin 4 -> ze} (d:∀ k,M k∈zP L/\∀ j,M k (0,j)=if j=k then 1 else 0) (l:∀ S∈zh L 0,∀ b,z7 0 0 (M 0+S) 0 b=z7 0 0 (M 0+S) 1 b) (s:∀ k b,M (z8 0 k) (1,z8 0 b)-M (z8 0 k) (2,z8 0 b)=0):False:=by
 refine yR i q r λ T m j n=>?_;obtain⟨b,rfl⟩:=j4 0 j n;set Y:=T-∑ k,T (0,z8 0 k)•M (z8 0 k)-T (0,0)•M 0;have f:∀ k j,M k (0,j)=if j=k then 1 else 0:=λ k=>(d k).2
 have a:∀ c,Y (0,c)=0:=λ c=>by simp only[Y,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,f,sum_univ_three];fin_cases c<;>simp[z8,f]
 have g:Y∈zh L 0:=⟨jQ i ((zP L).sub_mem ((zP L).sub_mem (mem_sup_left m) (Submodule.sum_mem _ λ k _=>(zP L).smul_mem _ (d _).1)) ((zP L).smul_mem _ (d 0).1)) a,LinearMap.mem_ker.2 (funext a)⟩;have o:=l Y g b;have p:=l 0 (Submodule.zero_mem _) b;simp only[zt,Pi.add_apply,add_zero,show z8 0 0=1 from rfl,show z8 0 1=2 from rfl] at o p;have h:T=Y+∑ k,T (0,z8 0 k)•M (z8 0 k)+T (0,0)•M 0:=by simp only[Y];abel
 have e:∀ k,M (z8 0 k) (1,z8 0 b)=M (z8 0 k) (2,z8 0 b):=by grind
 rw[h];simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_univ_three,e];grind
lemma P8 (e:zg L) (y:finrank KD L=6) (z:finrank KD (L.map (z9 0))=3) {l:(Fin 4->KD) →ₗ[KD] KD} (A:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (E:l (Pi.single 0 1)≠0) (i:y7∈L) (o:2≤finrank KD ((zh L 0).map (z7 0 0))):False:=by
 have⟨M,c⟩:=QJ e z A;have f:24*y4 (M 0)^4≠0:=by grind
 have m:=λ S (d:S∈zh L 0)=>QK e (c 0).1 (c 0).2.1 d;have p:∀ S∈zh L 0,M 0+S∈zP L:=λ S d=>(zP L).add_mem (c 0).1 (mem_sup_left d.1);by_cases g:∀ S∈zh L 0,∀ b,qZ (M 0+S) 0 b=qZ (M 0+S) 1 b
 . set G:Fin 3 -> Fin 3->KD:=λ k b=>M (z8 0 k) (1,z8 0 b)-M (z8 0 k) (2,z8 0 b)
   have q:∀ k b,M (z8 0 k) (0,z8 0 b)=if b=k then 1 else 0:=λ k b=>by rw[(c _).2.1];fin_cases k<;>fin_cases b<;>simp[z8]
   have I:=λ X (w:X∈zP L) S (d:S∈zh L 0)=>P3 e i (c 0).1 (c 0).2.1 g w d;have r:∀ k,∑ b,G k b=0:=λ k=>by have:=(w8 e i (c (z8 0 k)).1).1;simp only[sum_univ_three,G];exact this
   by_cases n:∀ k b,G k b=0
   . exact P7 e y i (λ k=>⟨(c k).1,(c k).2.1⟩) g n
   push Not at n;have⟨C,D,s⟩:=n;by_cases h:∃ k l,G k 0*G l 1-G k 1*G l 0≠0
   . have⟨k,l,u⟩:=h;exact P5 f m o g G (λ k S d=>(I _ (c (z8 0 k)).1 S d).1) r u
   . push Not at h
     refine P6 e f m o g G r (λ k j t S d=>?_) s h;have:=(I _ ((zP L).add_mem (c (z8 0 k)).1 ((zP L).smul_mem t (c (z8 0 j)).1)) S d).2;rw[show(λ b=>(M (z8 0 k)+t•M (z8 0 j)) (0,z8 0 b))=λ b=>(if b=k then (1:KD) else 0)+t*(if b=j then 1 else 0) from funext λ b=>by
      simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,q],
      show(λ b=>(M (z8 0 k)+t•M (z8 0 j)) (1,z8 0 b)-(M (z8 0 k)+t•M (z8 0 j)) (2,z8 0 b))=λ b=>G k b+t*G j b from funext λ b=>by simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,G];ring] at this
     exact this
 . refine P2 e f m o (λ S d k=>?_) (λ S d=>?_) g
   . have:=QL e (c 0).1 (c 0).2.1 k (c (z8 0 k)).1 (c (z8 0 k)).2.1 d i (λ a b x=>by simp[y7,x]) (by simp[y7]);simp[y7,sum_univ_three,z8,-map_add] at this;linear_combination this
   . have B:∀ j,S (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 d.2) j
     have v:=(w8 e i (p S d)).1;simp only[yX,Pi.add_apply] at v;simp only[sum_univ_three,zt,Pi.add_apply,z8,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons];linear_combination v
open LinearMap in
lemma xJ (hL:zg L) (h6:finrank KD L=6) {i:Fin 4} (h3:finrank KD (L.map (z9 i))=3) {l:(Fin 4->KD) →ₗ[KD] KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (i,j))=a) (p q:Perm (Fin 4)) (hp:p 0=i):zg (L.map (zq p q:ze →ₗ[KD] ze))/\finrank KD (L.map (zq p q:ze →ₗ[KD] ze))=6/\finrank KD ((L.map (zq p q:ze →ₗ[KD] ze)).map (z9 0))=3/\∀ a,∀ T∈L.map (zq p q:ze →ₗ[KD] ze),(l.comp (funLeft KD KD q.symm)) (λ j=>a+T (0,j))=a:=by
 refine⟨zH hL p q,(zF L p q).trans h6,?_,?_⟩
 . have e:(L.map (zq p q:ze →ₗ[KD] ze)).map (z9 0)=(L.map (z9 i)).map (funLeft KD KD q):=by
    rw[←map_comp,←map_comp];congr 1;ext X b;simp[zA,zy,hp]
   rw[e,←h3];exact(equivMapOfInjective _ (funLeft_injective_of_surjective _ _ _ q.surjective) _).finrank_eq.symm
 . rintro a _ ⟨T,c,rfl⟩;rw[LinearMap.comp_apply];exact(congrArg l (funext λ b=>by simp[zy,hp,funLeft_apply])).trans (hl a T c)
lemma xK {X:ze} (e:∀ s,X (0,s)=0) (f:z7 0 0 X=0):∀ r s,s≠0 -> X (r,s)=0:=λ r s d=>by
 by_cases c:r=0
 . rw[c];exact e s
 obtain⟨a,rfl⟩:=j4 0 r c;obtain⟨b,rfl⟩:=j4 0 s d;exact congrFun (congrFun f a) b
lemma P9 (hL:zg L) (h6:finrank KD L=6) (h3:finrank KD (L.map (z9 0))=3) {l:(Fin 4->KD) →ₗ[KD] KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (h0:l (Pi.single 0 1)≠0) (hZ1:finrank KD (zh L 0⊓LinearMap.ker (z7 0 0):Submodule KD ze)≤1) (p:Perm (Fin 4)) (hp0:p 0=0) {Zv:ze} (hZv:Zv∈L) {γ:KD} (hγ:γ≠0) (hpc:∀ r s,s≠0 -> Zv (r,s)=0) (h00:Zv (0,0)=0) (h1:Zv (p 1,0)=γ) (h2:Zv (p 2,0) = -γ) (h3':Zv (p 3,0)=0):False:=by
 have⟨f,e,c,g⟩:=xJ hL h6 h3 hl p 1 hp0;set d:=L.map (zq p 1:ze →ₗ[KD] ze);refine P8 f e c g (by rw[LinearMap.comp_apply];exact h0) ⟨γ⁻¹•Zv,L.smul_mem _ hZv,funext λ ⟨r,s⟩=>?_⟩ ?_
 . simp only[LinearEquiv.coe_coe,zy,Pi.smul_apply,smul_eq_mul,y7,Perm.coe_one,id];fin_cases r<;>fin_cases s<;>simp[hp0,h00,h1,h2,h3',hγ,hpc]
 . have t:finrank KD (zh d 0)=3:=by
    have:=zW (z9 0) d;rw[c,e] at this;show finrank KD (d⊓LinearMap.ker (z9 0):Submodule KD ze)=3;omega
   have q:finrank KD (zh d 0⊓LinearMap.ker (z7 0 0):Submodule KD ze)≤1:=by
    refine le_trans (le_of_eq_of_le (equivMapOfInjective ((zq p 1).symm:ze →ₗ[KD] ze) (zq p 1).symm.injective _).finrank_eq (finrank_mono ?_)) hZ1;rintro _ ⟨Y,⟨⟨h,i⟩,k⟩,rfl⟩;obtain⟨X,n,rfl⟩:=h;have m:∀ s,zq p 1 X (0,s)=0:=λ s=>congrFun (LinearMap.mem_ker.1 i) s;have o:=xK m (LinearMap.mem_ker.1 k);simp only[LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply];refine⟨⟨n,LinearMap.mem_ker.2 (funext λ s=>?_)⟩,LinearMap.mem_ker.2 (funext λ a=>funext λ b=>?_)⟩
    . have:=m s;simp only[zy,hp0,Perm.coe_one,id] at this;exact this
    . have:=o (p.symm (z8 0 a)) (z8 0 b) (by fin_cases b<;>decide);simp only[zy,apply_symm_apply,Perm.coe_one,id] at this;exact this
   have:=zW (z7 0 0) (zh d 0);omega
def ju:Fin 3 -> Perm (Fin 4):=![swap 1 2*swap 2 3,swap 2 3,1]
lemma w9:∀ c:Fin 3,ju c 0=0/\ju c 1=z8 0 (z6 c 0)/\ju c 2=z8 0 (z6 c 1)/\ju c 3=z8 0 c:=by decide
open LinearMap in
lemma Pa (y:zg L) (h6:finrank KD L=6) (h3:finrank KD (L.map (z9 0))=3) {l:(Fin 4->KD) →ₗ[KD] KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (h0:l (Pi.single 0 1)≠0):zh L 0⊓ker (z7 0 0)=⊥:=by
 set K:=zh L 0;set D:=qZ;set Z:=K⊓ker D;have hK:finrank KD K=3:=by have:=zW (z9 0) L;rw[h3,h6] at this;show finrank KD (L⊓ker (z9 0):Submodule KD ze)=3;omega
 have a3:finrank KD (K.map D)+finrank KD Z=3:=by have:=zW D K;rw[hK] at this;exact this
 have i:∀ X∈Z,(∀ r s,s≠0 -> X (r,s)=0)/\X (0,0)=0/\X (1,0)+X (2,0)+X (3,0)=0:=λ X m=>by have r0:∀ s,X (0,s)=0:=λ s=>congrFun (mem_ker.1 m.1.2) s;have H:=xK r0 (mem_ker.1 m.2);have p1:=(qb y m.1.1).1;simp only[qY,Fintype.sum_prod_type,sum_univ_four,r0,H _ 1 (by decide),H _ 2 (by decide),H _ 3 (by decide)] at p1;grind
 set ζ:ze →ₗ[KD] (Fin 2->KD):=LinearMap.pi ![proj (1,0),proj (2,0)];have hζ:Z⊓ker ζ=⊥:=(Submodule.eq_bot_iff _).2 λ X m=>by
  have⟨z,A,I⟩:=i X m.1;have B:=congrFun (mem_ker.1 m.2) 0;have o:=congrFun (mem_ker.1 m.2) 1;simp[ζ] at B o;funext ⟨r,s⟩;by_cases C:s=0
  . subst C;fin_cases r;exacts[A,B,o,show X (3,0)=0 by linear_combination I-B-o]
  . exact z r s C
 have u:=zW ζ Z;rw[hζ,finrank_bot,add_zero] at u;have a5:finrank KD Z≤2:=by rw[←u];exact(finrank_le _).trans (by simp)
 by_contra a4;have a6:1≤finrank KD Z:=by simp_all
 have⟨M,q⟩:=QJ y h3 hl;have E:24*y4 (M 0)^4≠0:=by grind
 have hP:∀ Sm∈K.map D,zo (D (M 0)+Sm)=24*y4 (M 0)^4:=by rintro _ ⟨S,J,rfl⟩;rw[←map_add];exact QK y (q 0).1 (q 0).2.1 J
 have N:∀ d∈Z,∀ Sm∈K.map D,∀ k,∑ a,d (z8 0 a,0)*zn (D (M 0)+Sm) a k=0:=by rintro d g _ ⟨S,J,rfl⟩ k;rw[←map_add];exact QL y (q 0).1 (q 0).2.1 k (q (z8 0 k)).1 (q (z8 0 k)).2.1 J g.1.1 (i d g).1 (i d g).2.1
 rcases Nat.lt_or_ge (finrank KD Z) 2 with h1|h2
 . have⟨d,g,O⟩:=exists_mem_ne_zero_of_ne_bot a4
   have⟨z,A,I⟩:=i d g;by_cases hz:d (z8 0 0,0)*d (z8 0 1,0)*d (z8 0 2,0)≠0
   . have:=QS (D (M 0)) (K.map D) (λ a=>d (z8 0 a,0)) hz E hP (N d g);omega
   push Not at hz;have⟨c,hc⟩:∃ c,d (z8 0 c,0)=0:=by grind
   have⟨q0,q1,q2,q3⟩:=w9 c;have C:d (ju c 1,0)+d (ju c 2,0)=0:=by
    have e:=qU (λ a=>d (z8 0 a,0)) c;have B:∑ a,d (z8 0 a,0)=0:=by simp only[sum_univ_three];exact I
    grind
   have hγ:d (ju c 1,0)≠0:=λ h'=>O (funext λ ⟨r,s⟩=>by
    by_cases F:s=0
    . subst F
      have G:d (ju c 2,0)=0:=by grind
      rw[q1] at h';rw[q2] at G;by_cases hr:r=0
      . rw[hr];exact A
      obtain⟨b,rfl⟩:=j4 0 r hr;obtain h|h|h:=jk c b<;>rw[h]
      exacts[hc,h',G]
    . exact z r s F)
   have P:finrank KD Z≤1:=by omega
   exact P9 y h6 h3 hl h0 P (ju c) q0 g.1.1 hγ z A rfl (by linear_combination C) (by rw[q3];exact hc)
 . have h2:finrank KD Z=2:=by omega
   have n:Z.map ζ=⊤:=eq_top_of_finrank_eq (by rw[u,h2];simp);have⟨Q,v,o⟩:(![1,-1]:Fin 2->KD)∈Z.map ζ:=n ▸ mem_top;have⟨R,w,e2⟩:(![0,1]:Fin 2->KD)∈Z.map ζ:=n ▸ mem_top;have U:=congrFun o 0;have V:=congrFun o 1;have W:=congrFun e2 0;have Y:=congrFun e2 1;simp[ζ] at U V W Y;have c1:=(i Q v).2.2;have c2:=(i R w).2.2;have⟨S0,x,a0⟩:=exists_mem_ne_zero_of_ne_bot (p:=K.map D) λ h=>by rw[h,finrank_bot] at a3;omega
   refine a0 (WU (D (M 0)) S0 E (λ t=>hP _ ((K.map D).smul_mem t x)) λ t k a a'=>?_);have w1:=N Q v _ ((K.map D).smul_mem t x) k;have w2:=N R w _ ((K.map D).smul_mem t x) k;simp only[sum_univ_three,z8,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons,U,V,W,Y] at w1 w2;rw[show Q (3,0)=0 by linear_combination c1-U-V,show R (3,0) = -1 by linear_combination c2-W-Y] at *;have f:∀ a,zn (D (M 0)+t•S0) a k=zn (D (M 0)+t•S0) 0 k:=λ a=>by fin_cases a<;>grind
   rw[f a,f a']
open LinearMap in
lemma qs (hL:zg L) (h6:finrank KD L=6) {i:Fin 4} (h3:finrank KD (L.map (z9 i))=3) {l:(Fin 4->KD) →ₗ[KD] KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (i,j))=a) {j:Fin 4} (hj:l (Pi.single j 1)≠0):zh L i⊓ker (z7 i j)=⊥:=by
 have⟨e,f,g,k⟩:=xJ hL h6 h3 hl (swap 0 i) (swap 0 j) (swap_apply_left 0 i);have m:=Pa e f g k (by
  rw[LinearMap.comp_apply]
  convert hj using 2;funext b
  simp only[funLeft_apply,Pi.single_apply,symm_swap];by_cases h:b=j
  . subst h;simp
  . have p:swap 0 j b≠0:=by
     grind
    simp[h,p])
 refine(Submodule.eq_bot_iff _).2 λ X d=>(zq (swap 0 i) (swap 0 j)).injective ((Submodule.eq_bot_iff _).1 m _ ⟨⟨⟨X,d.1.1,rfl⟩,mem_ker.2 (funext λ b=>?_)⟩,mem_ker.2 (funext λ a=>funext λ b=>?_)⟩ |>.trans (map_zero _).symm)
 . have:=congrFun (mem_ker.1 d.1.2) (swap 0 j b);simpa[zA,zy] using this
 . have q:=mem_ker.1 d.2
   simp only[LinearEquiv.coe_coe,zy,zt,Pi.zero_apply];have r:swap 0 i (z8 0 a)≠i:=by intro h;rw[swap_apply_eq_iff,swap_apply_right] at h;exact(by fin_cases a<;>decide:z8 0 a≠0) h
   have c:swap 0 j (z8 0 b)≠j:=by intro h;rw[swap_apply_eq_iff,swap_apply_right] at h;exact(by fin_cases b<;>decide:z8 0 b≠0) h
   have⟨s,n⟩:=j4 i _ r;have⟨t,o⟩:=j4 j _ c;rw[←n,←o];exact congrFun (congrFun q s) t
open LinearMap in
lemma qS (hL:zg L) (h6:finrank KD L=6) {j:Fin 4} (h3:finrank KD (L.map (zD j))=3) {m:(Fin 4->KD) →ₗ[KD] KD} (hm:∀ a,∀ T∈L,m (λ i=>a+T (i,j))=a) {i:Fin 4} (hi:m (Pi.single i 1)≠0):zC L j⊓ker (z7 i j)=⊥:=by
 set f:=L.map (zM:ze →ₗ[KD] ze);have d:finrank KD (f.map (z9 j))=3:=by rw[←map_comp,show z9 j ∘ₗ (zM:ze →ₗ[KD] ze)=zD j from LinearMap.ext λ X=>rfl];exact h3
 have e:=qs (zX hL) ((zT L).trans h6) d (l:=m) (by rintro a _ ⟨T,g,rfl⟩;exact hm a T g) hi;refine(Submodule.eq_bot_iff _).2 λ X c=>zM.injective ((Submodule.eq_bot_iff _).1 e _ ⟨⟨⟨X,c.1.1,rfl⟩,mem_ker.2 (funext λ b=>congrFun (mem_ker.1 c.1.2) b)⟩,mem_ker.2 (funext λ a=>funext λ b=>congrFun (congrFun (mem_ker.1 c.2) b) a)⟩ |>.trans (map_zero _).symm)
lemma j5 (a:Fin 3):z8 0 a=a.succ:=by fin_cases a<;>rfl
def zw:ze →ₗ[KD] Fin 3->KD where
 toFun Y b:=Y (0,b.succ)-Y (0,0)
 map_add' X Y:=by funext b;simp only[Pi.add_apply];ring
 map_smul' c X:=by funext b;simp only[Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring
abbrev yT:=zw
def zB:ze →ₗ[KD] Fin 3->KD where
 toFun Y a:=Y (a.succ,0)-Y (0,0)
 map_add' X Y:=by funext b;simp only[Pi.add_apply];ring
 map_smul' c X:=by funext b;simp only[Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring
abbrev yW:=zB
lemma qw (Y:ze) (b:Fin 3):zw Y b=Y (0,b.succ)-Y (0,0):=rfl
lemma qn (Y:ze) (a:Fin 3):zB Y a=Y (a.succ,0)-Y (0,0):=rfl
def zv (Y:ze):zx:=λ a b=>Y (a.succ,b.succ)-Y (0,0)
abbrev wN:=zv
def zE (M:zx) (x y:Fin 3->KD):KD:=∑ a,∑ b,y a*M a b*x b
def qT:ze →ₗ[KD] (Fin 3->KD) × (Fin 3->KD):=LinearMap.prod zw zB
lemma qL (X:ze) (a b:Fin 3):z7 0 0 X a b=X (a.succ,b.succ):=by rw[zt,j5,j5]
open LinearMap in
lemma qJ {T:ze} (h:T∈zm L 0 0):T∈L/\(∀ j,T (0,j)=0)/\∀ i,T (i,0)=0:=⟨h.1.1,λ j=>congrFun (mem_ker.1 h.1.2) j,λ i=>congrFun (mem_ker.1 h.2.2) i⟩
open LinearMap in
lemma yc {T:ze} (h:T∈L) (hr:∀ j,T (0,j)=0) (hc:∀ i,T (i,0)=0):T∈zm L 0 0:=⟨⟨h,mem_ker.2 (funext hr)⟩,⟨h,mem_ker.2 (funext hc)⟩⟩
lemma kJ (h:zg L) {Y Z:ze} (i:Y∈L) (j:Z∈zm L 0 0):zE (zn (zv Y+z7 0 0 Z)) (zw Y) (zB Y)=24*Y (0,0)^4:=by
 have⟨c,d,f⟩:=qJ j;have e:=qP h (L.add_mem i c) (-Y (0,0));rw[wJ] at e;simp only[Pi.add_apply,d,f,add_zero,neg_add_cancel,zero_mul,zero_add] at e;have g:(λ a b:Fin 3=>-Y (0,0)+(Y (a.succ,b.succ)+Z (a.succ,b.succ)))=zv Y+z7 0 0 Z:=by funext a b;simp only[zv,qL,Pi.add_apply];ring
 rw[g] at e;simp only[zE,qw,qn];grind
lemma Pb (A B:zx) (i j:Fin 3):zn (A+B) i j+zn (A-B) i j-2*zn A i j=2*zn B i j:=by simp only[zK,Pi.add_apply,Pi.sub_apply];ring
lemma qG (hL:zg L) {Y T:ze} (hY:Y∈L) (hT:T∈zm L 0 0):zE (zn (z7 0 0 T)) (zw Y) (zB Y)=0/\zE (zp (zv Y) (z7 0 0 T)) (zw Y) (zB Y)=0:=by
 have f:=kJ hL hY hT;have c:=kJ hL hY ((zm L 0 0).neg_mem hT);have d:=kJ hL hY (zm L 0 0).zero_mem;rw[map_neg,←sub_eq_add_neg] at c;rw[map_zero,add_zero] at d;have e:zE (zn (qZ T)) (yT Y) (yW Y)=0:=by
  have:2*zE (zn (qZ T)) (yT Y) (yW Y)=zE (zn (wN Y+qZ T)) (yT Y) (yW Y)+zE (zn (wN Y-qZ T)) (yT Y) (yW Y)-2*zE (zn (wN Y)) (yT Y) (yW Y):=by simp only[zE,Finset.mul_sum,←sum_add_distrib,←sum_sub_distrib];refine sum_congr rfl λ a _=>sum_congr rfl λ b _=>?_;linear_combination -(yW Y a*yT Y b)*Pb (wN Y) (qZ T) a b
  grind
 refine⟨e,?_⟩;have:zE (zp (wN Y) (qZ T)) (yT Y) (yW Y)=zE (zn (wN Y+qZ T)) (yT Y) (yW Y)-zE (zn (wN Y)) (yT Y) (yW Y)-zE (zn (qZ T)) (yT Y) (yW Y):=by simp only[zE,zp,←sum_sub_distrib];grind
 grind
lemma jl (hL:zg L) {Y:ze} (hY:Y∈L) (hx:zw Y=0):∀ j,Y (0,j)=0:=by
 have a:∀ j,Y (0,j)=Y (0,0):=λ j=>by refine cases rfl (λ b=>?_) j;have:=congrFun hx b;rw[qw] at this;simpa[sub_eq_zero] using this
 by_contra! h;have⟨j,d⟩:=h;have c:Y (0,0)≠0:=by rwa[←a j]
 exact qg hL 0 ⟨(Y (0,0))⁻¹•Y,L.smul_mem _ hY,funext λ k=>by simp[zA,a k,c]⟩
lemma Pc (d:zg L) {Y:ze} (e:Y∈L) (f:zB Y=0):∀ i,Y (i,0)=0:=by
 have a:∀ i,Y (i,0)=Y (0,0):=λ i=>by refine cases rfl (λ b=>?_) i;have:=congrFun f b;rw[qn] at this;simpa[sub_eq_zero] using this
 by_contra! h;have⟨i,g⟩:=h;have c:Y (0,0)≠0:=by rwa[←a i]
 exact jz d 0 ⟨(Y (0,0))⁻¹•Y,L.smul_mem _ e,funext λ k=>by simp[qF,a k,c]⟩
open LinearMap in
lemma vq (e:zg L):L⊓ker qT=zm L 0 0:=by
 ext Y;constructor
 . rintro⟨c,f⟩
   have d:yT Y=0/\yW Y=0:=by simpa[qT,Prod.ext_iff] using mem_ker.1 f
   exact yc c (jl e c d.1) (Pc e c d.2)
 . intro h;have⟨c,g,i⟩:=qJ h;exact⟨c,mem_ker.2 (Prod.ext (funext λ b=>by simp[qT,qw,g]) (funext λ a=>by simp[qT,qn,i]))⟩
lemma qz (hL:zg L) (hr:finrank KD (L.map (z9 0))=3):∀ x,∃ Y∈L,zw Y=x:=λ x=>by have⟨a,T,f,c⟩:=(qu hL hr).1 (Fin.cons 0 x);have d:=congrFun c 0;simp only[cons_zero] at d;refine⟨T,f,funext λ b=>?_⟩;have e:=congrFun c b.succ;simp only[cons_succ] at e;rw[qw];linear_combination -e+d
lemma qX (hL:zg L) (hc:finrank KD (L.map (zD 0))=3):∀ y,∃ Y∈L,zB Y=y:=λ y=>by have⟨a,T,f,c⟩:=(j3 hL hc).1 (Fin.cons 0 y);have d:=congrFun c 0;simp only[cons_zero] at d;refine⟨T,f,funext λ b=>?_⟩;have e:=congrFun c b.succ;simp only[cons_succ] at e;rw[qn];linear_combination -e+d
lemma ym (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3):(∀ Y∈L,∀ T∈zm L 0 0,zE (zn (z7 0 0 T)) (zw Y) (zB Y)=0/\zE (zp (zv Y) (z7 0 0 T)) (zw Y) (zB Y)=0)/\(∀ x,∃ Y∈L,zw Y=x)/\(∀ y,∃ Y∈L,zB Y=y)/\L⊓LinearMap.ker qT=zm L 0 0/\finrank KD (L.map qT)+finrank KD (zm L 0 0)=6:=by refine⟨λ Y a T b=>qG hL a b,qz hL hr,qX hL hc,vq hL,?_⟩;rw[←vq hL,←h6];exact zW _ _
lemma xL (M:zx) (a b:Fin 3):zE M (Pi.single b 1) (Pi.single a 1)=M a b:=by fin_cases a<;>fin_cases b<;>simp[zE,sum_univ_three]
def jd (M:zx):(Fin 3->KD) →ₗ[KD] (Fin 3->KD) →ₗ[KD] KD :=
 LinearMap.mk₂ KD (zE M)
  (λ x x' y=>by simp only[zE,Pi.add_apply,sum_univ_three];ring)
  (λ c x y=>by simp only[zE,Pi.smul_apply,smul_eq_mul,sum_univ_three];ring)
  (λ x y y'=>by simp only[zE,Pi.add_apply,sum_univ_three];ring)
  (λ c x y=>by simp only[zE,Pi.smul_apply,smul_eq_mul,sum_univ_three];ring)
open LinearMap in
lemma jA {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (φ:V →ₗ[KD] KD) (hφ:φ≠0):finrank KD (ker φ)+1=finrank KD V:=by have e:=φ.finrank_range_add_finrank_ker;have a:=finrank_le (LinearMap.range φ);rw[finrank_self] at a;have b:finrank KD (LinearMap.range φ)≠0:=λ h=>hφ (range_eq_bot.1 (finrank_eq_zero.1 h));omega
open LinearMap in
lemma Pd (W:Submodule KD ((Fin 3->KD) × (Fin 3->KD))) (j:finrank KD W=5) (hx:∀ x,∃ y,(x,y)∈W) (v:∀ y,∃ x,(x,y)∈W) (M:zx) (w:∀ p∈W,zE M p.1 p.2=0):M=0:=by
 have q:finrank KD ((Fin 3->KD) × (Fin 3->KD))=6:=by simp
 have k:W<⊤:=lt_top_iff_ne_top.2 λ h=>by rw[h,finrank_top,q] at j;norm_num at j
 have⟨φ,i,l⟩:=W.exists_le_ker_of_lt_top k;have r:finrank KD (ker φ)=5:=by have:=jA φ i;omega
 have s:W=ker φ:=eq_of_le_of_finrank_le l (by rw[r,j]);set f:=φ.comp (inl KD _ _);set g:=-φ.comp (inr KD _ _);have e:∀ x y,φ (x,y)=f x-g y:=λ x y=>by rw[show(x,y)=(x,0)+(0,y) by simp,map_add];simp[f,g]
 have d:∀ x y,(x,y)∈W↔f x=g y:=λ x y=>by rw[s,mem_ker,e,sub_eq_zero]
 have⟨x0,m⟩:∃ x,f x≠0:=by by_contra! h;apply i;refine LinearMap.ext λ p=>?_;have⟨t,c⟩:=v p.2;rw[d,h] at c;rw[LinearMap.zero_apply,show p=(p.1,p.2) from rfl,e,h,←c,sub_self]
 have⟨y0,n⟩:∃ y,g y≠0:=by by_contra! h;apply i;refine LinearMap.ext λ p=>?_;have⟨t,c⟩:=hx p.1;rw[d,h] at c;rw[LinearMap.zero_apply,show p=(p.1,p.2) from rfl,e,h,c,sub_self]
 have u:=qC (jd M) f g (x0:=(f x0)⁻¹•x0) (y0:=(g y0)⁻¹•y0) (by simp[m]) (by simp[n]) λ x y o=>w (x,y) ((d x y).2 o);funext a b;rw[←xL M a b];exact u _ _
lemma yv (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd1:finrank KD (zm L 0 0)=1):∀ T∈zm L 0 0,zn (z7 0 0 T)=0:=λ T e=>by
 obtain⟨b,c,d,-,f⟩:=ym hL h6 hr hc;refine Pd (L.map qT) (by omega) (λ x=>?_) (λ y=>?_) _ ?_
 . obtain⟨Y,a,rfl⟩:=c x;exact⟨yW Y,Y,a,rfl⟩
 . obtain⟨Y,a,rfl⟩:=d y;exact⟨yT Y,Y,a,rfl⟩
 . rintro _ ⟨Y,a,rfl⟩;exact(b Y a T e).1
lemma Pe (M:Matrix (Fin 3) (Fin 3) KD) (h:∀ x:Fin 3->KD,∑ a,∑ b,x a*M a b*x b=0):M.transpose = -M:=by ext i j;have c:=h (Pi.single i 1);have d:=h (Pi.single j 1);have e:=h (Pi.single i 1+Pi.single j 1);fin_cases i<;>fin_cases j<;>simp[sum_univ_three] at c d e⊢<;>grind
lemma y5 (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3):finrank KD (zh L 0)=3:=by have:=zW (z9 0) L;rw[hr,h6] at this;exact Nat.add_left_cancel (this.trans rfl)
lemma Pf (a:finrank KD L=6) (b:finrank KD (L.map (zD 0))=3):finrank KD (zC L 0)=3:=by have:=zW (zD 0) L;rw[b,a] at this;exact Nat.add_left_cancel (this.trans rfl)
open LinearMap in
lemma Pg (m:zg L) (n:finrank KD L=6) (o:finrank KD (L.map (z9 0))=3) (u:finrank KD (L.map (zD 0))=3) (p:finrank KD (zm L 0 0)=3):∃ F:Matrix (Fin 3) (Fin 3) KD,IsUnit F.det/\(∀ Y∈L,zB Y=F.mulVec (zw Y))/\(∃ s:(Fin 3->KD) →ₗ[KD] ze,∀ x,s x∈L/\zw (s x)=x)/\∀ T∈zm L 0 0,(F.transpose*of (zn (z7 0 0 T))).transpose = -(F.transpose*of (zn (z7 0 0 T))):=by
 obtain⟨e,g,h,-,-⟩:=ym m n o u;have q:zm L 0 0=zh L 0:=eq_of_le_of_finrank_le inf_le_left (by rw[y5 n o,p]);have⟨i,j⟩:=(yT.domRestrict L).exists_rightInverse_of_surjective (by rw[range_eq_top];intro x;obtain⟨Y,b,rfl⟩:=g x;exact⟨⟨Y,b⟩,rfl⟩);set s:=L.subtype ∘ₗ i;have c:∀ x,s x∈L/\yT (s x)=x:=λ x=>⟨(i x).2,by have:=LinearMap.congr_fun j x;simpa[s] using this⟩;set F:=toMatrix' (yW ∘ₗ s);have v:∀ x,F.mulVec x=yW (s x):=λ x=>by simp[F,toMatrix'_mulVec]
 have d:∀ Y∈L,yW Y=F.mulVec (yT Y):=λ Y b=>by
  have f:Y-s (yT Y)∈L:=L.sub_mem b (c _).1;have k:yT (Y-s (yT Y))=0:=by grind
  have r:Y-s (yT Y)∈zm L 0 0:=by rw[q];exact⟨f,mem_ker.2 (funext (jl m f k))⟩
  obtain⟨-,-,l⟩:=qJ r;have:yW (Y-s (yT Y))=0:=funext λ a=>by simp[qn,l]
  grind
 refine⟨F,?_,d,⟨s,c⟩,λ T t=>Pe _ λ x=>?_⟩
 . rw[←Matrix.isUnit_iff_isUnit_det,←mulVec_surjective_iff_isUnit];intro y;obtain⟨Y,b,rfl⟩:=h y;exact⟨_,(d Y b).symm⟩
 . have:=(e (s x) (c x).1 T t).1;rw[d _ (c x).1,(c x).2] at this;simp only[zE,mulVec,dotProduct,Matrix.mul_apply,transpose_apply,of_apply,sum_univ_three] at this⊢;linear_combination this
lemma j6 {T:zx} (hC:zn T=0) {a a' b b':Fin 3} (ha:a≠a') (hb:b≠b'):T a b*T a' b'+T a b'*T a' b=0:=by
 have⟨k,c⟩:=w5 a a' ha;have⟨l,d⟩:=w5 b b' hb;have h:zn T k l=0:=by rw[hC];rfl
 rw[zK] at h;grind
lemma xM:∀ a a':Fin 3,a≠a'->∃ r,r≠a/\r≠a'/\∀ x,x=a\/x=a'\/x=r:=by decide
lemma qd (T:zx) (hT:T≠0) (hC:zn T=0):(∃ r0,∀ r,r≠r0->∀ c,T r c=0)\/(∃ c0,∀ c,c≠c0->∀ r,T r c=0)\/∃ r0 c0,(∀ c,T r0 c=0)/\(∀ r,T r c0=0)/\(∀ r,r≠r0->∀ c,c≠c0 -> T r c≠0)/\T (z6 r0 0) (z6 c0 0)*T (z6 r0 1) (z6 c0 1)+T (z6 r0 0) (z6 c0 1)*T (z6 r0 1) (z6 c0 0)=0/\T (z6 r0 0) (z6 c0 0)*T (z6 r0 1) (z6 c0 1)-T (z6 r0 0) (z6 c0 1)*T (z6 r0 1) (z6 c0 0)≠0:=by
 by_cases k:∃ r0,∀ r,r≠r0->∀ c,T r c=0
 . exact Or.inl k
 by_cases l:∃ c0,∀ c,c≠c0->∀ r,T r c=0
 . exact Or.inr (Or.inl l)
 right;right;push Not at k l;have⟨a,b,C⟩:∃ a b,T a b≠0:=by by_contra! h;exact hT (funext λ a=>funext λ b=>h a b)
 have⟨K,D,c,y⟩:=k a;have⟨f,g,i,j,d,e,L,M⟩:∃ f g i j,f≠i/\g≠j/\T f g≠0/\T i j≠0:=by
  by_cases p:c=b
  . subst p;have⟨E,z,F,A⟩:=l c;grind
  grind
 have⟨r0,m,q,n⟩:=xM f i d;have⟨c0,o,s,t⟩:=xM g j e;have G:=j6 hC d e;have N:T f g*T i j-T f j*T i g≠0:=by grind
 have u:T f j*T i g≠0:=λ h=>by grind
 have H:=(mul_ne_zero_iff.1 u).1;have I:=(mul_ne_zero_iff.1 u).2;have O:=j6 hC (m.symm) e;have P:=j6 hC (q.symm) e;have Q:=j6 hC d (o.symm);have R:=j6 hC d (s.symm);have S:T r0 g=0:=by grind
 have U:T r0 j=0:=by grind
 have V:T f c0=0:=by grind
 have W:T i c0=0:=by grind
 have X:T r0 c0=0:=by have Y:=j6 hC (m.symm) (o.symm);grind
 have v:∀ x,T r0 x=0:=λ x=>by rcases t x with rfl|rfl|rfl<;>assumption
 have w:∀ x,T x c0=0:=λ x=>by rcases n x with rfl|rfl|rfl<;>assumption
 have J:∀ r,r≠r0->∀ c,c≠c0 -> T r c≠0:=λ r Z c y=>by rcases n r with rfl|rfl|rfl<;>grind
 have⟨s1,s2,s3⟩:=zN r0;have⟨t1,t2,t3⟩:=zN c0;have B:zn T r0 c0=0:=by rw[hC];rfl
 rw[zK] at B;grind
def qj (k:Fin 3):ze →ₗ[KD] KD:=(LinearMap.proj k:(Fin 3->KD) →ₗ[KD] KD) ∘ₗ zw
def qq (k:Fin 3):ze →ₗ[KD] KD:=(LinearMap.proj k:(Fin 3->KD) →ₗ[KD] KD) ∘ₗ zB
def yg (r c:Fin 3):ze →ₗ[KD] KD where
 toFun Y:=zv Y r c
 map_add' X Y:=by simp only[zv,Pi.add_apply];ring
 map_smul' a X:=by simp only[zv,Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring
def ke:ze →ₗ[KD] KD where
 toFun Y:=-Y (0,0)
 map_add' X Y:=by simp only[Pi.add_apply];ring
 map_smul' a X:=by simp only[Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring
def qf (v:Fin 3->KD):(Fin 3->KD) →ₗ[KD] KD where
 toFun x:=∑ k,v k*x k
 map_add' x y:=by simp only[Pi.add_apply,sum_univ_three];ring
 map_smul' a x:=by simp only[Pi.smul_apply,smul_eq_mul,RingHom.id_apply,sum_univ_three];ring
lemma qQ (v:Fin 3->KD) (j:Fin 3) (s:KD):∑ k,v k*(Pi.single j s:Fin 3->KD) k=v j*s:=by simp[Pi.single_apply]
lemma kK {l:(Fin 4->KD) →ₗ[KD] KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) {Y:ze} (hY:Y∈L):∑ k,l (Pi.single k.succ 1)*zw Y k = -Y (0,0):=by have e:=hl (-Y (0,0)) Y hY;rw[show(λ j=>-Y (0,0)+Y (0,j))=∑ k:Fin 3,yT Y k•(Pi.single k.succ 1:Fin 4->KD) by funext j;fin_cases j<;>simp[sum_univ_three,qw]<;>ring] at e;rw[map_sum] at e;simp only[map_smul,smul_eq_mul] at e;rw[←e];grind
lemma vr {m:(Fin 4->KD) →ₗ[KD] KD} (hm:∀ a,∀ T∈L,m (λ i=>a+T (i,0))=a) {Y:ze} (hY:Y∈L):∑ k,m (Pi.single k.succ 1)*zB Y k = -Y (0,0):=by have e:=hm (-Y (0,0)) Y hY;rw[show(λ i=>-Y (0,0)+Y (i,0))=∑ k:Fin 3,yW Y k•(Pi.single k.succ 1:Fin 4->KD) by funext j;fin_cases j<;>simp[sum_univ_three,qn]<;>ring] at e;rw[map_sum] at e;simp only[map_smul,smul_eq_mul] at e;rw[←e];grind
open LinearMap in
lemma vs (hL:zg L) (h6:finrank KD L=6) (hd1:finrank KD (zm L 0 0)=1) (lam mu:Fin 3->KD) (hlm:∀ Y∈L,∑ k,lam k*zw Y k=∑ k,mu k*zB Y k) (hne:lam≠0):∀ x y,∑ k,lam k*x k=∑ k,mu k*y k->∃ Y∈L,zw Y=x/\zB Y=y:=by
 set ψ:(Fin 3->KD) × (Fin 3->KD) →ₗ[KD] KD:=(qf lam).comp (LinearMap.fst KD _ _)-(qf mu).comp (LinearMap.snd KD _ _);have c:ψ≠0:=by intro h;apply hne;funext k;have:=LinearMap.congr_fun h (Pi.single k 1,0);simpa[ψ,qf,qQ] using this
 have g:=jA ψ c;have f:finrank KD ((Fin 3->KD) × (Fin 3->KD))=6:=by simp
 have d:L.map qT=ker ψ:=by
  apply eq_of_le_of_finrank_le
  . rintro _ ⟨Y,a,rfl⟩;simp only[mem_ker,ψ,LinearMap.sub_apply,LinearMap.comp_apply];simp[qf,qT,hlm Y a]
  . have:=zW qT L;rw[vq hL,hd1,h6] at this;omega
 intro x y b;have:(x,y)∈L.map qT:=by rw[d];simp[ψ,qf,b]
 have⟨Y,a,e⟩:=this;exact⟨Y,a,congrArg Prod.fst e,congrArg Prod.snd e⟩
lemma xN {E:Type} [AddCommGroup E] [Module KD E] (Q:E →ₗ[KD] E →ₗ[KD] KD) (x y:E) (t:KD):Q (x+t•y) (x+t•y)=Q x x+t*(Q x y+Q y x)+t^2*Q y y:=by simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];ring
lemma yh {E:Type} [AddCommGroup E] [Module KD E] (N:Submodule KD E) (u:E →ₗ[KD] KD) (Q:E →ₗ[KD] E →ₗ[KD] KD) {e:E} (he:e∈N) (hue:u e=1) (h:∀ x∈N,u x*Q x x=0):∀ x∈N,Q x x=0:=by
 intro x a;obtain⟨-,b,c,d⟩:=qE (u x*Q x x) (Q x x+u x*(Q x e+Q e x)) ((Q x e+Q e x)+u x*Q e e) (Q e e) λ t=>by have:=h _ (N.add_mem a (N.smul_mem t he));rw[map_add,map_smul,xN,hue] at this;simp only[smul_eq_mul,mul_one] at this;linear_combination this
 grind
lemma kf {E:Type} [AddCommGroup E] [Module KD E] (N:Submodule KD E) (f:E →ₗ[KD] KD) (Q:E →ₗ[KD] E →ₗ[KD] KD) {e:E} (he:e∈N) (hqe:Q e e≠0) (h:∀ x∈N,f x*Q x x=0):∀ x∈N,f x=0:=by
 intro x a;obtain⟨b,c,-,-⟩:=qE (f e*Q e e) (f e*(Q e x+Q x e)+f x*Q e e) (f e*Q x x+f x*(Q e x+Q x e)) (f x*Q x x) λ t=>by have:=h _ (N.add_mem he (N.smul_mem t a));rw[map_add,map_smul,xN] at this;simp only[smul_eq_mul] at this;linear_combination this
 grind
lemma zJ (k:Fin 3) (Y:ze):qj k Y=zw Y k:=rfl
lemma zG (k:Fin 3) (Y:ze):qq k Y=zB Y k:=rfl
lemma qx (r c:Fin 3) (Y:ze):yg r c Y=zv Y r c:=rfl
lemma kL (Y:ze):ke Y = -Y (0,0):=rfl
lemma xO {c d e f:KD} (g:c≠0\/d≠0) (h:∀ y1 y2:KD,c*y1+d*y2=1 -> e*y1+f*y2=0):e=0/\f=0:=by
 rcases g with i|j
 . have a:=h c⁻¹ 0 (by field_simp;ring);have b:=h ((1-d)/c) 1 (by field_simp;ring);grind
 . have a:=h 0 d⁻¹ (by field_simp;ring);have b:=h 1 ((1-c)/d) (by field_simp;ring);grind
lemma Ph (A B:zx) (x y:Fin 3->KD) {r0 f d e a b:Fin 3} (i:z6 r0 0=d) (j:z6 r0 1=e) (k:z6 f 0=a) (l:z6 f 1=b) (g:∀ c,B r0 c=0) (h:∀ r,B r f=0) (m:y r0=0):zE (zp A B) x y=A r0 f*(y d*(B e b*x a+B e a*x b)+y e*(B d b*x a+B d a*x b))+x f*(y d*(B e a*A r0 b+B e b*A r0 a)+y e*(B d a*A r0 b+B d b*A r0 a)):=by subst i j k l;fin_cases r0<;>fin_cases f<;>simp at g h m<;>simp[zE,zR,z6,sum_univ_three,g,h,m]<;>ring
lemma vu (A:zx) (x y:Fin 3->KD) {r0 c0 i1 i2 j1 j2:Fin 3} (hi1:z6 r0 0=i1) (hi2:z6 r0 1=i2) (hj1:z6 c0 0=j1) (hj2:z6 c0 1=j2) (hx:x c0=0) (hy:y r0=0) (hA:A r0 c0=0):zE (zn A) x y=(y i1*A i2 c0+y i2*A i1 c0)*(x j1*A r0 j2+x j2*A r0 j1):=by subst hi1 hi2 hj1 hj2;fin_cases r0<;>fin_cases c0<;>simp at hx hy hA<;>simp[zE,zK,z6,sum_univ_three,hx,hy,hA]<;>ring
lemma yO (Z Y:ze) (r c:Fin 3):zv (Z+Y) r c=zv Z r c+zv Y r c:=by simp only[zv,Pi.add_apply];ring
lemma jm (Z Y:ze) (r c:Fin 3):zv (Z-Y) r c=zv Z r c-zv Y r c:=by simp only[zv,Pi.sub_apply];ring
lemma jn {a b c d u v:KD} (hD:a*d-b*c≠0) (h1:a*u+b*v=0) (h2:c*u+d*v=0):u=0/\v=0:=⟨(mul_eq_zero.1 (show(a*d-b*c)*u=0 by linear_combination d*h1-b*h2)).resolve_left hD,(mul_eq_zero.1 (show(a*d-b*c)*v=0 by linear_combination a*h2-c*h1)).resolve_left hD⟩
def yi {E:Type} [AddCommGroup E] [Module KD E] (u1 v1 u2 v2:E →ₗ[KD] KD):E →ₗ[KD] E →ₗ[KD] KD:=u1.smulRight v1+u2.smulRight v2
lemma zU {E:Type} [AddCommGroup E] [Module KD E] (u1 v1 u2 v2:E →ₗ[KD] KD) (x y:E):yi u1 v1 u2 v2 x y=u1 x*v1 y+u2 x*v2 y:=by simp[yi]
open LinearMap in
lemma yn (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd1:finrank KD (zm L 0 0)=1) {l m:(Fin 4->KD) →ₗ[KD] KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (hm:∀ a,∀ T∈L,m (λ i=>a+T (i,0))=a) {T:ze} (hT:T∈zm L 0 0) {r0 c0:Fin 3} (h0r:∀ c,z7 0 0 T r0 c=0) (h0c:∀ r,z7 0 0 T r c0=0) (hnz:∀ r,r≠r0->∀ c,c≠c0 -> z7 0 0 T r c≠0) (hla:l (Pi.single (z6 c0 0).succ 1)≠0\/l (Pi.single (z6 c0 1).succ 1)≠0) (hma:m (Pi.single (z6 r0 0).succ 1)≠0\/m (Pi.single (z6 r0 1).succ 1)≠0):False:=by
 have hC:=yv hL h6 hr hc hd1 T hT;have R:zn (z7 0 0 T) r0 c0=0:=by rw[hC];rfl
 rw[zK] at R;have⟨s1,s2,s3⟩:=zN r0;have⟨t1,t2,t3⟩:=zN c0;have nb:=hnz _ (s1.symm) _ (t1.symm);have nc:=hnz _ (s1.symm) _ (t2.symm);have nd:=hnz _ (s2.symm) _ (t1.symm);have ne:=hnz _ (s2.symm) _ (t2.symm);have⟨p,E,a8⟩:∃ p:Fin 3->KD,(∀ Y∈L,∑ k,p k*zw Y k = -Y (0,0))/\∀ k,p k=l (Pi.single k.succ 1):=⟨_,λ Y o=>kK hl o,λ k=>rfl⟩;have⟨x,d4,a9⟩:∃ x:Fin 3->KD,(∀ Y∈L,∑ k,x k*zB Y k = -Y (0,0))/\∀ k,x k=m (Pi.single k.succ 1):=⟨_,λ Y o=>vr hm o,λ k=>rfl⟩;rw[←a8,←a8] at hla;rw[←a9,←a9] at hma;have sr:∀ f:Fin 3->KD,∑ k,f k=f r0+f (z6 r0 0)+f (z6 r0 1):=λ f=>qU f r0;have sc:∀ f:Fin 3->KD,∑ k,f k=f c0+f (z6 c0 0)+f (z6 c0 1):=λ f=>qU f c0;have M:=λ Y (o:Y∈L)=>(qG hL o hT).2;have f2:=λ Y (o:Y∈L)=>kJ hL o (zm L 0 0).zero_mem;generalize z7 0 0 T=B at M h0r h0c R nb nc nd ne;generalize b0:z6 r0 0=g at *;generalize b1:z6 r0 1=n at *;generalize b2:z6 c0 0=b at *;generalize b3:z6 c0 1=d at *;have b4:∀ Y∈L,zB Y r0=0 -> zv Y r0 c0*(zB Y g*(B n d*zw Y b+B n b*zw Y d)+zB Y n*(B g d*zw Y b+B g b*zw Y d))+zw Y c0*(zB Y g*(B n b*zv Y r0 d+B n d*zv Y r0 b)+zB Y n*(B g b*zv Y r0 d+B g d*zv Y r0 b))=0:=λ Y o d5=>by rw[←Ph _ _ _ _ b0 b1 b2 b3 h0r h0c d5];exact M Y o
 have d6:∀ Y∈L,zw Y c0=0 -> zB Y r0=0 -> zv Y r0 c0=0->(zB Y g*zv Y n c0+zB Y n*zv Y g c0)*(zw Y b*zv Y r0 d+zw Y d*zv Y r0 b)=24*(-Y (0,0))^4:=λ Y o H C hA=>by rw[←vu _ _ _ b0 b1 b2 b3 H C hA];grind
 have c4:∀ u v:KD,B n d*u+B n b*v=0 -> B g d*u+B g b*v=0 -> u=0/\v=0:=λ u v=>jn (by rw[show B n d*B g b-B n b*B g d=2*(B g b*B n d) by linear_combination -R];exact mul_ne_zero two_ne_zero (mul_ne_zero nb ne));have⟨w,d7,b5⟩:∃ j,(j=b\/j=d)/\p j≠0:=by grind
 have⟨F,f4,f5⟩:∃ i,(i=g\/i=n)/\x i≠0:=by grind
 have S:c0≠w:=by grind
 have I:r0≠F:=by grind
 have hW:=vs hL h6 hd1 p x (λ Y o=>(E Y o).trans (d4 Y o).symm) (λ h=>b5 (congrFun h w));have J:∀ (j i:Fin 3) (s s':KD),p j*s=x i*s'->∃ Y∈L,zw Y=Pi.single j s/\zB Y=Pi.single i s':=λ j i s s' h=>hW _ _ (by rw[qQ,qQ,h]);have K:∀ q t:KD,(q•Pi.single g 1+t•Pi.single n 1:Fin 3->KD) r0=0/\(q•Pi.single g 1+t•Pi.single n 1:Fin 3->KD) g=q/\(q•Pi.single g 1+t•Pi.single n 1:Fin 3->KD) n=t:=λ q t=>by simp[s1,s2,s3,s3.symm]
 have d8:∀ q t:KD,∑ k,x k*(q•Pi.single g 1+t•Pi.single n 1:Fin 3->KD) k=x g*q+x n*t:=λ q t=>by grind
 set z:=L⊓ker (qj c0)⊓ker (qq r0) with f6
 have A:∀ Y,Y∈z↔Y∈L/\zw Y c0=0/\zB Y r0=0:=λ Y=>by simp only[z,Submodule.mem_inf,mem_ker,zJ,zG,and_assoc]
 have hξ:∀ Y∈z,zv Y r0 c0=0:=by
  set Qb:=yi (qq g) (B n d•qj b+B n b•qj d) (qq n) (B g d•qj b+B g b•qj d);have b6:∀ Y,Qb Y Y=zB Y g*(B n d*zw Y b+B n b*zw Y d)+zB Y n*(B g d*zw Y b+B g b*zw Y d):=λ Y=>by simp[Qb,zU,zJ,zG]
  have⟨Y0,d9,e0⟩:∃ Y0∈z,Qb Y0 Y0≠0:=by
   by_contra! U;have f3:p b*(Pi.single w (p w)⁻¹:Fin 3->KD) b+p d*(Pi.single w (p w)⁻¹:Fin 3->KD) d=1:=by grind
   have V:∀ q t:KD,x g*q+x n*t=1->(B n d*(Pi.single w (p w)⁻¹:Fin 3->KD) b+B n b*(Pi.single w (p w)⁻¹:Fin 3->KD) d)*q+(B g d*(Pi.single w (p w)⁻¹:Fin 3->KD) b+B g b*(Pi.single w (p w)⁻¹:Fin 3->KD) d)*t=0:=λ q t b7=>by have⟨Y,o,H,C⟩:=hW (Pi.single w (p w)⁻¹) (q•Pi.single g 1+t•Pi.single n 1) (by grind);have:=U Y ((A Y).2 ⟨o,by rw[H];exact single_eq_of_ne S _,by rw[C];exact(K q t).1⟩);rw[b6,H,C,(K q t).2.1,(K q t).2.2] at this;linear_combination this
   have⟨W,e2⟩:=xO hma V;grind
  refine kf z (yg r0 c0) Qb d9 e0 λ Y o=>?_;have⟨D,H,C⟩:=(A Y).1 o;have:=b4 Y D C;rw[H,zero_mul,add_zero] at this;rw[b6,qx];linear_combination this
 have⟨Y1,b8,X,b9⟩:=J c0 F 1 (p c0/x F) (by field_simp);have⟨Y2,e3,c1,e4⟩:=J w r0 (x r0/p w) 1 (by field_simp);have e5:∀ Y∈L,zv Y r0 c0=zv Y1 r0 c0*zw Y c0+zv Y2 r0 c0*zB Y r0:=λ Y o=>by have N:Y-zw Y c0•Y1-zB Y r0•Y2∈z:=(A _).2 ⟨L.sub_mem (L.sub_mem o (L.smul_mem _ b8)) (L.smul_mem _ e3),by simp[map_sub,map_smul,X,c1,S],by simp[map_sub,map_smul,b9,e4,I]⟩;have:=hξ _ N;simp only[zv,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at this⊢;linear_combination this
 set η:=zv Y1 r0 c0;have⟨y,a0,O,e6⟩:=J w F (p w)⁻¹ (x F)⁻¹ (by grind);have G:y∈z:=(A _).2 ⟨a0,by rw[O];exact single_eq_of_ne S _,by rw[e6];exact single_eq_of_ne I _⟩;have a3:ke y=1:=by have:=E y a0;rw[O,qQ,mul_inv_cancel₀ b5] at this;rw[kL,←this]
 have⟨c',f7,a4⟩:=jG z (yi (qj b) (yg r0 d) (qj d) (yg r0 b)) (yi (qq g) (yg n c0) (qq n) (yg g c0)) ke G a3 λ Y o=>by have⟨D,H,C⟩:=(A Y).1 o;have:=d6 Y D H C (hξ Y o);simp only[zU,zJ,zG,qx,kL];linear_combination this
 have⟨Z1,e7,a5,c5⟩:=J b F 1 (p b/x F) (by field_simp);have⟨Z2,e8,a6,c6⟩:=J d F 1 (p d/x F) (by field_simp);have c7:Z1∈z:=(A _).2 ⟨e7,by rw[a5];exact single_eq_of_ne t1 _,by rw[c5];exact single_eq_of_ne I _⟩;have c8:Z2∈z:=(A _).2 ⟨e8,by rw[a6];exact single_eq_of_ne t2 _,by rw[c6];exact single_eq_of_ne I _⟩;have e9:∀ Y∈z,zw Y=0 -> zv Y r0 b=0/\zv Y r0 d=0:=by
  have c2:∀ Y∈z,zw Y=0->∀ Z∈z,zw Z b*zv Y r0 d+zw Z d*zv Y r0 b=0:=λ Y o P Z hZ=>by
   have f0:ke Y=0:=by have:=E Y ((A Y).1 o).1;rw[P] at this;simp at this;simp[kL,this]
   have c9:zw (Z+Y)=zw Z:=by grind
   have W:=(a4 (Z+Y) (z.add_mem hZ o)).1;have e2:=(a4 Z hZ).1;simp only[map_add ke,f0,add_zero] at W;simp only[zU,zJ,qx,c9,yO] at W e2;grind
  intro Y o P;have a1:=c2 Y o P Z1 c7;have a2:=c2 Y o P Z2 c8;rw[a5,single_eq_same,single_eq_of_ne (t3.symm)] at a1;rw[a6,single_eq_same,single_eq_of_ne t3] at a2;grind
 have f1:∀ Y∈L⊓ker (qq r0),zB Y g*(B n d*(η*zw Y b+zv Y r0 b)+B n b*(η*zw Y d+zv Y r0 d))+zB Y n*(B g d*(η*zw Y b+zv Y r0 b)+B g b*(η*zw Y d+zv Y r0 d))=0:=by
  set Q:=η•yi (qq g) (B n d•qj b+B n b•qj d) (qq n) (B g d•qj b+B g b•qj d)+yi (qq g) (B n b•yg r0 d+B n d•yg r0 b) (qq n) (B g b•yg r0 d+B g d•yg r0 b);have hQ:∀ Y,Q Y Y=zB Y g*(B n d*(η*zw Y b+zv Y r0 b)+B n b*(η*zw Y d+zv Y r0 d))+zB Y n*(B g d*(η*zw Y b+zv Y r0 b)+B g b*(η*zw Y d+zv Y r0 d)):=λ Y=>by simp only[Q,LinearMap.add_apply,LinearMap.smul_apply,zU,zJ,zG,qx,smul_eq_mul];ring
  intro Y o;rw[←hQ];refine yh (L⊓ker (qq r0)) (qj c0) Q (e:=Y1) (Submodule.mem_inf.2 ⟨b8,mem_ker.2 (by
   rw[zG,b9];exact single_eq_of_ne I _)⟩)
   (by rw[zJ,X,single_eq_same]) (λ Y o=>?_) Y o
  have⟨D,C⟩:=Submodule.mem_inf.1 o;have C:=mem_ker.1 C;rw[zG] at C;have:=b4 Y D C;rw[e5 Y D,C,mul_zero,add_zero] at this;rw[hQ,zJ];linear_combination this
 have d0:=((A y).1 G).2.1;have V:∀ q t:KD,x g*q+x n*t=1->(B n d*(η*zw y b+zv y r0 b)+B n b*(η*zw y d+zv y r0 d))*q+(B g d*(η*zw y b+zv y r0 b)+B g b*(η*zw y d+zv y r0 d))*t=0:=by intro q t b7;have⟨Y',N,c3,a7⟩:=hW (zw y) (q•Pi.single g 1+t•Pi.single n 1) (by rw[E y a0,d8,b7,←kL,a3]);have d3:Y'∈z:=(A _).2 ⟨N,by rw[c3];exact d0,by rw[a7];exact(K q t).1⟩;have⟨d1,d2⟩:=e9 _ (z.sub_mem d3 G) (by grind);rw[jm,sub_eq_zero] at d1 d2;have:=f1 Y' (Submodule.mem_inf.2 ⟨N,mem_ker.2 (by rw[zG,a7];exact(K q t).1)⟩);rw[c3,a7,(K q t).2.1,(K q t).2.2,d1,d2] at this;linear_combination this
 have⟨W,e2⟩:=xO hma V;have⟨f8,f9⟩:=c4 _ _ W e2;have hq:=(a4 y G).1;rw[zU,zJ,zJ,qx,qx,a3,one_pow,mul_one] at hq;rcases d7 with h|h
 . have c1:zw y d=0:=by rw[O,h];exact single_eq_of_ne (t3.symm) _
   grind
 . have X:zw y b=0:=by rw[O,h];exact single_eq_of_ne t3 _
   grind
lemma Pj (r:ℝ) (a:0≤r):∃ ρ:ℝ,ρ^3=r:=by obtain⟨ρ,-,b⟩:=intermediate_value_Icc (by linarith:(0:ℝ)≤r+1) (f:=λ x:ℝ=>x^3) (continuous_pow 3).continuousOn ⟨by simpa using a,by nlinarith[sq_nonneg r,mul_nonneg a (sq_nonneg r)]⟩;exact⟨ρ,b⟩
lemma Pk (α:ℝ) (h:α^2≤1):∃ c:ℝ,c^2≤1/\4*c^3-3*c=α:=by
 have e : -1≤α:=by nlinarith
 have g:α≤1:=by nlinarith
 obtain⟨c,⟨b,d⟩,a⟩:=intermediate_value_Icc (by norm_num:(-1:ℝ)≤1) (f:=λ x:ℝ=>4*x^3-3*x) (by fun_prop) ⟨by norm_num;linarith,by norm_num;linarith⟩;exact⟨c,by nlinarith,a⟩
lemma xP (w:KD):∃ z:KD,z^3=w:=by
 by_cases g:w=0
 . exact⟨0,by simp[g]⟩
 set a:=w.re;set b:=w.im;set r:=Real.sqrt (a^2+b^2);have i:r^2=a^2+b^2:=Real.sq_sqrt (by positivity);have e:r≠0:=by intro h;rw[h] at i;apply g;apply Complex.ext<;>simp<;>nlinarith
 have⟨c,k,n⟩:=Pk (a/r) (by rw[div_pow,div_le_one (by positivity)];nlinarith);set d:=Real.sqrt (1-c^2);have f:d^2=1-c^2:=by grind
 have j:(d*(3-4*d^2))^2=(b/r)^2:=by grind
 have⟨s,l,m⟩:∃ s:ℝ,s^2=1-c^2/\s*(3-4*s^2)=b/r:=by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 j with h|h
  . exact⟨d,f,h⟩
  . exact⟨-d,by rw[neg_sq,f],by linear_combination -h⟩
 have⟨ρ,o⟩:=Pj r (Real.sqrt_nonneg _);have p:a/r*r=a:=div_mul_cancel₀ a e;have q:b/r*r=b:=div_mul_cancel₀ b e;refine⟨⟨ρ*c,ρ*s⟩,Complex.ext ?_ ?_⟩
 . simp only[pow_succ,pow_zero,one_mul,Complex.mul_re,Complex.mul_im];grind
 . simp only[pow_succ,pow_zero,one_mul,Complex.mul_re,Complex.mul_im];grind
lemma Pl (p q:KD):∃ u:KD,u^3+p*u+q=0:=by
 have⟨s,d⟩:=jj (q^2/4+p^3/27);by_cases e:p=0
 . have⟨u,f⟩:=xP (-q);exact⟨u,by rw[f,e];ring⟩
 have g : -q/2+s≠0:=by grind
 have⟨v,a⟩:=xP (-q/2+s);have h:v≠0:=by grind
 have⟨k,b⟩:∃ k,3*v*k=p:=⟨p/(3*v),by field_simp⟩;have c:(-q/2+s)*k^3=p^3/27:=by rw[←a,←b];ring
 refine⟨v-k,(mul_eq_zero.1 (show(-q/2+s)*((v-k)^3+p*(v-k)+q)=0 by linear_combination d+(-q/2+s)*a-c-(-q/2+s)*(v-k)*b)).resolve_left g⟩
lemma Pm (d c b a:KD) (f:a≠0):∃ t:KD,d+c*t+b*t^2+a*t^3=0:=by
 have⟨u,e⟩:=Pl ((3*a*c-b^2)/(3*a^2)) ((2*b^3-9*a*b*c+27*a^2*d)/(27*a^3));refine⟨u-b/(3*a),?_⟩;have:d+c*(u-b/(3*a))+b*(u-b/(3*a))^2+a*(u-b/(3*a))^3=a*(u^3+(3*a*c-b^2)/(3*a^2)*u+(2*b^3-9*a*b*c+27*a^2*d)/(27*a^3)):=by field_simp;ring
 rw[this,e,mul_zero]
lemma vv (a b c:KD):∃ s t:KD,(s≠0\/t≠0)/\a*s^2+b*s*t+c*t^2=0:=by
 by_cases d:a=0
 . exact⟨1,0,Or.inl one_ne_zero,by simp[d]⟩
 have⟨w,e⟩:=jj (b^2-4*a*c);refine⟨(-b+w)/(2*a),1,Or.inr one_ne_zero,?_⟩;grind
lemma xQ (B:(Fin 3->KD) →ₗ[KD] (Fin 3->KD) →ₗ[KD] KD) (x y:Fin 3->KD):B x y=∑ a,∑ b,x a*y b*B (Pi.single a 1) (Pi.single b 1):=by
 have e:∀ z:Fin 3->KD,z=z 0•Pi.single 0 1+z 1•Pi.single 1 1+z 2•Pi.single 2 1:=λ z=>by funext i;fin_cases i<;>simp
 conv_lhs=>rw[e x,e y]
 simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,sum_univ_three];ring
lemma Pn (e b:Matrix (Fin 3) (Fin 3) KD):∃ α β:KD,(α≠0\/β≠0)/\∃ k:Fin 3->KD,k≠0/\(α•e+β•b).mulVec k=0:=by
 by_cases d:b.det=0
 . have⟨k,c,a⟩:=exists_mulVec_eq_zero_iff.2 d;exact⟨0,1,Or.inr one_ne_zero,k,c,by simpa using a⟩
 set P:KD->KD:=λ t=>(e+t•b).det;have⟨t,f⟩:=Pm (P 0) ((P 1-P (-1))/2-b.det) ((P 1+P (-1))/2-P 0) b.det d;have g:P t=0:=by rw[←f];simp only[P,det_fin_three,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul];ring
 have⟨k,c,a⟩:=exists_mulVec_eq_zero_iff.2 g;exact⟨1,t,Or.inl one_ne_zero,k,c,by simpa using a⟩
lemma Po (g i:(Fin 3->KD) →ₗ[KD] (Fin 3->KD) →ₗ[KD] KD):∃ x:Fin 3->KD,x≠0/\g x x=0/\i x x=0:=by
 have⟨α,β,n,k,z,o⟩:=Pn (of λ a b=>g (Pi.single a 1) (Pi.single b 1)+g (Pi.single b 1) (Pi.single a 1)) (of λ a b=>i (Pi.single a 1) (Pi.single b 1)+i (Pi.single b 1) (Pi.single a 1));set Q:=α•g+β•i;have A:∀ y,Q y k+Q k y=0:=λ y=>by have h:=λ a=>congrFun o a;simp only[mulVec,dotProduct,Matrix.add_apply,Matrix.smul_apply,of_apply,smul_eq_mul,sum_univ_three,Pi.zero_apply] at h;rw[xQ Q,xQ Q];simp only[Q,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,sum_univ_three];grind
 have⟨j,K⟩:∃ j,k j≠0:=by by_contra! h;exact z (funext h)
 have⟨B,C,q⟩:=zN j;have⟨s,t,G,D⟩:=vv (Q (Pi.single (zV j 0) 1) (Pi.single (zV j 0) 1)) (Q (Pi.single (zV j 0) 1) (Pi.single (zV j 1) 1)+Q (Pi.single (zV j 1) 1) (Pi.single (zV j 0) 1)) (Q (Pi.single (zV j 1) 1) (Pi.single (zV j 1) 1));set p:Fin 3->KD:=s•Pi.single (zV j 0) 1+t•Pi.single (zV j 1) 1;have r:p j=0:=by simp[p,B,C]
 have H:p≠0:=by intro h;have e:=congrFun h (zV j 0);have c:=congrFun h (zV j 1);simp[p,q,q.symm] at e c;grind
 have I:Q p p=0:=by simp only[p,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination D
 have J:Q k k=0:=by grind
 have u:∀ σ τ:KD,Q (σ•p+τ•k) (σ•p+τ•k)=0:=λ σ τ=>by have:=A p;simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];grind
 have v:∀ σ τ:KD,(σ≠0\/τ≠0)->σ•p+τ•k≠0:=λ σ τ l h=>by have:=congrFun h j;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,r,mul_zero,zero_add,Pi.zero_apply] at this;rcases mul_eq_zero.1 this with E|E<;>simp_all
 have f:∀ d:(Fin 3->KD) →ₗ[KD] (Fin 3->KD) →ₗ[KD] KD,∃ x,x≠0/\Q x x=0/\d x x=0:=λ d=>by have⟨σ,τ,l,F⟩:=vv (d p p) (d p k+d k p) (d k k);refine⟨σ•p+τ•k,v σ τ l,u σ τ,?_⟩;simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination F
 by_cases w:α=0
 . have L:=n.resolve_left (not_not.2 w);have⟨x,m,e,c⟩:=f g;refine⟨x,m,c,?_⟩;simp only[Q,w,zero_smul,zero_add,LinearMap.smul_apply,smul_eq_mul] at e;grind
 . have⟨x,m,e,c⟩:=f i;refine⟨x,m,?_,c⟩;simp only[Q,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,c,mul_zero,add_zero] at e;grind
lemma vx {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (N:Submodule KD V) (i:finrank KD N=3) (a d:V →ₗ[KD] V →ₗ[KD] KD):∃ x∈N,x≠0/\a x x=0/\d x x=0:=by let b:=finBasisOfFinrankEq KD N i;let ψ:(Fin 3->KD) →ₗ[KD] V:=N.subtype ∘ₗ b.equivFun.symm.toLinearMap;have⟨c,e,f,g⟩:=Po (a.compl₁₂ ψ ψ) (d.compl₁₂ ψ ψ);refine⟨ψ c,(b.equivFun.symm c).2,λ h=>e ?_,f,g⟩;have:b.equivFun.symm c=0:=Subtype.ext h;exact b.equivFun.symm.injective (by rw[this,map_zero])
open LinearMap in
lemma Pp {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (N:Submodule KD V) (E:finrank KD N=3) (f d:V →ₗ[KD] KD) (i m r:V →ₗ[KD] V →ₗ[KD] KD) (Q:∃ x∈N,f x≠0\/d x≠0) (F:∀ x∈N,f x*i x x+d x*m x x=0):∃ x∈N,x≠0/\i x x=0/\m x x=0/\r x x=0:=by
 have k:∀ (M:Submodule KD V) (u:V →ₗ[KD] KD) (x:V),x∈M -> u x≠0->∃ e∈M,u e=1:=λ M u x c h=>⟨(u x)⁻¹•x,M.smul_mem _ c,by simp[h]⟩;by_cases z:∀ x∈N,f x=0
 . have⟨G,g,R⟩:=Q
   have⟨e,A,n⟩:=k N d G g (R.resolve_left (not_not.2 (z G g)));have s:=yh N d m A n λ x c=>by grind
   have⟨x,c,S,a,b⟩:=vx N E i r;grind
 push Not at z;have⟨T,B,H⟩:=z;have⟨Y,I,C⟩:=k N f T B H;by_cases l:∃ κ:KD,∀ x∈N,d x=κ*f x
 . have⟨κ,l⟩:=l
   have U:=yh N f (i+κ•m) I C λ x c=>by have:=F x c;rw[l x c] at this;simp only[LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination this
   have⟨x,c,g,a,b⟩:=vx N E m r;refine⟨x,c,g,?_,a,b⟩;have:=U x c;simp only[LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,a,mul_zero,add_zero] at this;exact this
 push Not at l;have⟨W,D,J⟩:∃ x∈N,d x≠0:=by by_contra! h;have⟨y,K,t⟩:=l 0;exact t (by rw[h y K,zero_mul])
 have⟨j,v,o⟩:=k N d W D J;have p:∀ x∈N,x-d x•j∈N⊓ker d:=λ x c=>Submodule.mem_inf.2 ⟨N.sub_mem c (N.smul_mem _ v),by simp[o]⟩;have⟨e,A,n⟩:∃ e∈N⊓ker d,f e=1:=by
  by_contra! h;have X:∀ e∈N⊓ker d,f e=0:=by grind
  have Z:∀ x∈N,f x=f j*d x:=λ x c=>by have:=X _ (p x c);simp only[map_sub,map_smul,smul_eq_mul] at this;linear_combination this
  have hc:f j≠0:=by grind
  have⟨y,K,t⟩:=l (f j)⁻¹;grind
 have L:=yh (N⊓ker d) f i A n λ x c=>by have⟨O,P⟩:=Submodule.mem_inf.1 c;have:=F x O;rwa[mem_ker.1 P,zero_mul,add_zero] at this
 set h:V →ₗ[KD] KD:=i j+i.flip j-i j j•d;have q:∀ x∈N,i x x=d x*h x:=λ x c=>by have:=L _ (p x c);simp only[map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul] at this;simp only[h,LinearMap.sub_apply,LinearMap.add_apply,flip_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination this
 have s:=yh N d (f.smulRight h+m) v o λ x c=>by have:=F x c;rw[q x c] at this;simp only[LinearMap.add_apply,LinearMap.smulRight_apply,LinearMap.smul_apply,smul_eq_mul];linear_combination this
 have⟨x,c,g,a,b⟩:=vx N E r (h.smulRight h);simp only[LinearMap.smulRight_apply,LinearMap.smul_apply,smul_eq_mul] at b;have w:h x=0:=mul_self_eq_zero.1 b;refine⟨x,c,g,by rw[q x c,w,mul_zero],?_,a⟩;have:=s x c;simp only[LinearMap.add_apply,LinearMap.smulRight_apply,LinearMap.smul_apply,smul_eq_mul,w,mul_zero,zero_add] at this;exact this
lemma Pq {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (N:Submodule KD V) (p:finrank KD N=3) (B:Fin 3 -> V →ₗ[KD] V →ₗ[KD] KD) (l:Fin 3 -> V →ₗ[KD] KD) (c:Fin 3->KD) (q:c 2≠0) (f:∀ x∈N,∑ k,c k*l k x=0) (j:∃ k,∃ x∈N,l k x≠0) (r:∀ x∈N,∑ k,l k x*B k x x=0):∃ x∈N,x≠0/\∀ k,B k x x=0:=by
 have m:∃ x∈N,l 0 x≠0\/l 1 x≠0:=by have⟨k,x,e,s⟩:=j;refine⟨x,e,?_⟩;by_contra! h;have:=f x e;simp only[sum_univ_three,h.1,h.2,mul_zero,zero_add] at this;have t:=(mul_eq_zero.1 this).resolve_left q;fin_cases k<;>grind
 have g:∀ x∈N,l 0 x*(c 2•B 0-c 0•B 2) x x+l 1 x*(c 2•B 1-c 1•B 2) x x=0:=λ x e=>by have n:=f x e;have o:=r x e;simp only[sum_univ_three] at n o;simp only[LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul];grind
 have⟨x,e,i,a,b,d⟩:=Pp N p (l 0) (l 1) (c 2•B 0-c 0•B 2) (c 2•B 1-c 1•B 2) (B 2) m g;refine⟨x,e,i,λ k=>?_⟩;simp only[LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,d,mul_zero,sub_zero] at a b;fin_cases k<;>grind
lemma Pr {V:Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (N:Submodule KD V) (i:finrank KD N=3) (B:Fin 3 -> V →ₗ[KD] V →ₗ[KD] KD) (l:Fin 3 -> V →ₗ[KD] KD) (c:Fin 3->KD) (m:c≠0) (b:∀ x∈N,∑ k,c k*l k x=0) (e:∃ k,∃ x∈N,l k x≠0) (n:∀ x∈N,∑ k,l k x*B k x x=0):∃ x∈N,x≠0/\∀ k,B k x x=0:=by
 have⟨j,f⟩:∃ j,c j≠0:=by by_contra! h;exact m (funext h)
 have⟨x,a,d,h⟩:=Pq N i (λ k=>B (swap j 2 k)) (λ k=>l (swap j 2 k)) (λ k=>c (swap j 2 k)) (by simpa using f) (λ x a=>by rw[Equiv.sum_comp (swap j 2) (λ k=>c k*l k x)];exact b x a) (by have⟨k,x,a,g⟩:=e;exact⟨swap j 2 k,x,a,by simpa using g⟩) (λ x a=>by rw[Equiv.sum_comp (swap j 2) (λ k=>l k x*B k x x)];exact n x a);exact⟨x,a,d,λ k=>by simpa using h (swap j 2 k)⟩
open LinearMap in
def yj (i b:Fin 3):zx →ₗ[KD] KD :=
 (proj b:(Fin 3->KD) →ₗ[KD] KD) ∘ₗ (proj i:zx →ₗ[KD] (Fin 3->KD))
lemma yp (i b:Fin 3) (A:zx):yj i b A=A i b:=rfl
def kg (F:Matrix (Fin 3) (Fin 3) KD) (a b:Fin 3):zx →ₗ[KD] zx →ₗ[KD] KD :=
 LinearMap.mk₂ KD (λ A A'=>∑ x,F x a*zp A A' x b)
  (λ A A' A''=>by simp only[zR,Pi.add_apply,sum_univ_three];ring)
  (λ c A A'=>by simp only[zR,Pi.smul_apply,smul_eq_mul,sum_univ_three];ring)
  (λ A A' A''=>by simp only[zR,Pi.add_apply,sum_univ_three];ring)
  (λ c A A'=>by simp only[zR,Pi.smul_apply,smul_eq_mul,sum_univ_three];ring)
lemma Ps (F:Matrix (Fin 3) (Fin 3) KD) (a b:Fin 3) (A:zx):kg F a b A A=2*(F.transpose*of (zn A)) a b:=by simp only[kg,LinearMap.mk₂_apply,Matrix.mul_apply,transpose_apply,of_apply,zR,zK,sum_univ_three];ring
def vy (F:Matrix (Fin 3) (Fin 3) KD):Fin 3 -> zx →ₗ[KD] zx →ₗ[KD] KD :=
 ![kg F 0 1,kg F 0 2,kg F 1 2]
def kM (G:Matrix (Fin 3) (Fin 3) KD) (i:Fin 3):Fin 3 -> zx →ₗ[KD] KD :=
 ![G i 0•yj i 1-G i 1•yj i 0,G i 0•yj i 2-G i 2•yj i 0,
  G i 1•yj i 2-G i 2•yj i 1]
lemma wO {T:ze} (hr:∀ j,T (0,j)=0) (hc:∀ i,T (i,0)=0):qY T=∑ a,∑ b,z7 0 0 T a b/\jh T=zo (z7 0 0 T):=by
 constructor
 . simp[qY,Fintype.sum_prod_type,sum_univ_four,sum_univ_three,zt,z8,hr,hc]
 . simp[jh,sum_univ_four,zs,z8,zt,hr,hc]
lemma xR (G:Matrix (Fin 3) (Fin 3) KD) (a:G.det≠0) (i:Fin 3):∃ j,G i j≠0:=by by_contra! h;apply a;fin_cases i<;>simp at h<;>simp[det_fin_three,h]
open LinearMap in
lemma Pt (G:Matrix (Fin 3) (Fin 3) KD) (n:G.det≠0) (N:Submodule KD zx) (q:finrank KD N=3) (k:∀ A∈N,∑ a,∑ b,A a b=0) (r:∀ A∈N,∀ i a b,G i a*A i b=G i b*A i a):False:=by
 choose j s using xR G n;set κ:zx →ₗ[KD] (Fin 3->KD):=LinearMap.pi λ i=>(G i (j i))⁻¹•yj i (j i);have l:∀ A∈N,∀ i b,A i b=κ A i*G i b:=λ A c i b=>by simp only[κ,pi_apply,LinearMap.smul_apply,yp,smul_eq_mul];grind
 have f:Function.Injective (κ.domRestrict N):=by
  rw[←ker_eq_bot,eq_bot_iff];rintro⟨A,c⟩ h;have o:κ A=0:=by simpa using h
  rw[mem_bot];apply Subtype.ext;funext i b;show A i b=0;rw[l A c i b,o];simp
 have d:=(injective_iff_surjective_of_finrank_eq_finrank (by rw[q,finrank_fin_fun])).1 f;have p:∀ e,∑ b,G e b=0:=λ e=>by
  have⟨⟨A,c⟩,m⟩:=d (Pi.single e 1);have g:κ A=Pi.single e 1:=by simpa using m
  have:=k A c;rw[sum_congr rfl λ i _=>sum_congr rfl λ b _=>l A c i b,g] at this;simpa[Pi.single_apply] using this
 apply n;refine exists_mulVec_eq_zero_iff.1 ⟨λ _=>1,λ h=>by simpa using congrFun h 0,?_⟩;funext i;simp[mulVec,dotProduct,p i]
lemma Pu (G:Matrix (Fin 3) (Fin 3) KD) (S A:zx) (i:Fin 3) (d:∀ a b,zn A a b=∑ k,G a k*S k b) (f:∀ a b,S b a = -S a b) (e:zo A=0):(G i 0*A i 1-G i 1*A i 0)*(2*S 0 1)+(G i 0*A i 2-G i 2*A i 0)*(2*S 0 2)+(G i 1*A i 2-G i 2*A i 1)*(2*S 1 2)=0:=by have c:=jb A i;rw[e] at c;simp only[sum_univ_three,d] at c;grind
lemma Pv (F G:Matrix (Fin 3) (Fin 3) KD) (p:G*F.transpose=1) (N:Submodule KD zx) (q:finrank KD N=3) (g:∀ A∈N,∑ a,∑ b,A a b=0/\zo A=0/\(F.transpose*of (zn A)).transpose = -(F.transpose*of (zn A))):∃ A∈N,A≠0/\zn A=0:=by
 have t:G.det≠0:=λ h=>by have:=congrArg det p;rw[det_mul,h,zero_mul,det_one] at this;exact zero_ne_one this
 have u:∀ A∈N,∀ a b,(F.transpose*of (zn A)) b a =
  -(F.transpose*of (zn A)) a b:=λ A c a b=>by
  have:=congrFun (congrFun (g A c).2.2 a) b;simpa using this
 have v:∀ A:zx,∀ a b,zn A a b =
  ∑ k,G a k*(F.transpose*of (zn A)) k b:=λ A a b=>by
  have:=congrFun (congrFun (show of (zn A)=G*(F.transpose*of
   (zn A)) by rw[←Matrix.mul_assoc,p,Matrix.one_mul]) a) b
  rw[of_apply,Matrix.mul_apply] at this;exact this
 have e:∀ i k A,kM G i k A=![G i 0*A i 1-G i 1*A i 0,
  G i 0*A i 2-G i 2*A i 0,G i 1*A i 2-G i 2*A i 1] k:=λ i k A=>by
  fin_cases k<;>simp[kM,yp]
 have n:∀ k A,vy F k A A=![2*(F.transpose*of (zn A)) 0 1,
  2*(F.transpose*of (zn A)) 0 2,2*(F.transpose*of (zn A)) 1 2] k :=
  λ k A=>by fin_cases k<;>simp[vy,Ps]
 have⟨i,k,H,w,I⟩:∃ i k,∃ A∈N,kM G i k A≠0:=by
  by_contra! h;refine Pt G t N q (λ A c=>(g A c).1) λ A c i a b=>?_;have x:=h i 0 A c;have y:=h i 1 A c;have B:=h i 2 A c;rw[e] at x y B;simp only[cons_val_zero,cons_val_one,
   cons_val_two,head_cons,Matrix.tail_cons] at x y B
  fin_cases a<;>fin_cases b<;>simp only[zero_eta,mk_one,reduceFinMk] <;>
   grind
 have⟨J,f⟩:=xR G t i;have⟨A,c,r,s⟩:=Pr N q (vy F) (kM G i) ![G i 2,-G i 1,G i 0]
  (λ h=>by
   have C:=congrFun h 0;have D:=congrFun h 1;have E:=congrFun h 2;simp only[cons_val_zero,cons_val_one,cons_val_two,head_cons,
    Matrix.tail_cons,Pi.zero_apply,neg_eq_zero] at C D E
   fin_cases J;exacts[f E,f D,f C])
  (λ A _=>by
   simp only[sum_univ_three,e,cons_val_zero,cons_val_one,
    cons_val_two,head_cons,Matrix.tail_cons];ring)
  ⟨k,H,w,I⟩ (λ A c=>by
   simp only[sum_univ_three,e,n,cons_val_zero,cons_val_one,
    cons_val_two,head_cons,Matrix.tail_cons]
   exact Pu G _ A i (v A) (u A c) (g A c).2.1)
 refine⟨A,c,r,?_⟩;have j:=s 0;have l:=s 1;have m:=s 2;rw[n] at j l m;simp only[cons_val_zero,cons_val_one,cons_val_two,head_cons,
  Matrix.tail_cons,mul_eq_zero,two_ne_zero,false_or] at j l m
 have d:=u A c;have o:=v A;generalize F.transpose*of (zn A)=S at j l m d o;have z:∀ a b,S a b=0:=by
  have O:=d 0 0;have P:=d 1 1;have Q:=d 2 2;have K:=d 0 1;have L:=d 0 2;have M:=d 1 2;rw[j,neg_zero] at K;rw[l,neg_zero] at L;rw[m,neg_zero] at M;intro a b;fin_cases a<;>fin_cases b<;>simp only[zero_eta,mk_one,reduceFinMk] <;>
   grind
 funext a b;rw[o,sum_univ_three,z,z,z];simp
open LinearMap in
lemma j7:zm L 0 0⊓ker (z7 0 0)=⊥:=by
 rw[eq_bot_iff];intro T g;have⟨c,d⟩:=Submodule.mem_inf.1 g;obtain⟨-,e,f⟩:=qJ c;have h:=mem_ker.1 d;rw[mem_bot];funext ⟨i,j⟩;induction i using cases with
 | zero=>exact e j
 | succ a =>
  induction j using cases with
  | zero=>exact f _
  | succ b=>have:=congrFun (congrFun h a) b;rwa[qL] at this
lemma j8 (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd3:finrank KD (zm L 0 0)=3):∃ T∈zm L 0 0,T≠0/\zn (z7 0 0 T)=0:=by
 obtain⟨F,i,-,-,a⟩:=Pg hL h6 hr hc hd3;have c:finrank KD ((zm L 0 0).map (qZ))=3:=by have:=zW (qZ) (zm L 0 0);rw[j7,finrank_bot,hd3] at this;omega
 obtain⟨A,⟨T,b,rfl⟩,d,j⟩:=Pv F _ (nonsing_inv_mul _ (by rw[det_transpose];exact i)) _ c (by rintro _ ⟨T,b,rfl⟩;have⟨e,f,g⟩:=qJ b;obtain⟨k,-,l,-⟩:=qb hL e;have⟨m,n⟩:=wO f g;exact⟨m ▸ k,n ▸ l,a T b⟩);exact⟨T,b,λ h=>d (by rw[h,map_zero]),j⟩
def yw (L:Submodule KD ze) (M:zx):Prop :=
 ∀ Y∈L,zE M (zw Y) (zB Y)=0
lemma vA (M a:zx) (c:KD) (x y:Fin 3->KD):zE (M+c•a) x y=zE M x y+c*zE a x y:=by simp only[zE,Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_univ_three];ring
lemma kN {M b:zx} (h:yw L M) (d:yw L b) (c:KD):yw L (M+c•b):=λ Y a=>by rw[vA,h Y a,d Y a];ring
lemma yI (hL:zg L) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) {M:zx} (hB:yw L M) (hm:∀ a a' b b',M a b*M a' b'=M a b'*M a' b):M=0:=by
 by_contra g;have⟨c,d,i⟩:∃ a b,M a b≠0:=by by_contra! h;exact g (funext λ a=>funext (h a))
 have j:∀ Y∈L,(qf (λ a=>M a d) (yW Y))*(qf (λ b=>M c b) (yT Y))=0:=λ Y f=>by
  have e:(qf (λ a=>M a d) (yW Y))*(qf (λ b=>M c b) (yT Y))=M c d*zE M (yT Y) (yW Y):=by have l:∀ v w:Fin 3->KD,qf v w=∑ k,v k*w k:=λ _ _=>rfl;rw[l,l,sum_mul_sum,zE,Finset.mul_sum];refine sum_congr rfl λ a _=>?_;rw[Finset.mul_sum];grind
  rw[e,hB Y f,mul_zero]
 rcases zz L ((qf (λ a=>M a d)).comp yW) ((qf (λ b=>M c b)).comp yT) j with h|h
 . have⟨Y,f,m⟩:=qX hL hc (Pi.single c 1);have:=h Y f;simp only[LinearMap.comp_apply,m,qf,LinearMap.coe_mk,AddHom.coe_mk,qQ,mul_one] at this;exact i this
 . have⟨Y,f,n⟩:=qz hL hr (Pi.single d 1);have:=h Y f;simp only[LinearMap.comp_apply,n,qf,LinearMap.coe_mk,AddHom.coe_mk,qQ,mul_one] at this;exact i this
lemma qV {M:zx} (r:Fin 3) (h:∀ a,a≠r->∀ b,M a b=0):∀ a a' b b',M a b*M a' b'=M a b'*M a' b:=λ a a' b b'=>by grind
lemma jo {M:zx} (c:Fin 3) (h:∀ b,b≠c->∀ a,M a b=0):∀ a a' b b',M a b*M a' b'=M a b'*M a' b:=λ a a' b b'=>by grind
lemma xS (m:zg L) (n:finrank KD (L.map (z9 0))=3) {H:ze} (h:H∈zh L 0) {M:zx} (i:yw L M):∀ b,∑ a,zB H a*M a b=0:=λ b=>by
 have l:∀ j,H (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 h.2) j;have⟨Y,c,d⟩:=qz m n (Pi.single b 1);have e:=i _ (L.add_mem c h.1);have f:=i Y c;have g:yT H=0:=funext λ k=>by simp[qw,l]
 rw[map_add,map_add,g,add_zero,d] at e;rw[d] at f;have:=e.trans f.symm;simp only[zE,Pi.add_apply,sum_univ_three] at this;simp only[sum_univ_three];grind
open LinearMap in
lemma xT (V:zg L) (W:finrank KD L=6) (X:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (a0:finrank KD (zm L 0 0)=2):∃ x2 y1:Fin 3->KD,∀ M,yw L M -> zE M x2 y1=0 -> M=0:=by
 have hK:=y5 W X;have I:=Pf W hc;have hR:finrank KD ↥(zh L 0⊔zC L 0)=4:=by have:=finrank_sup_add_finrank_inf_eq (zh L 0) (zC L 0);rw[show zh L 0⊓zC L 0=zm L 0 0 from rfl,a0,hK,I] at this;omega
 have l:zh L 0⊔zC L 0≤L:=sup_le inf_le_left inf_le_left;have q:∀ R:Submodule KD ze,R≤L -> finrank KD R<6->∃ Y∈L,finrank KD ↥(R⊔span KD {Y})=finrank KD R+1:=by
  intro R l a1;have⟨Y,c,s⟩:∃ Y∈L,Y∉R:=by by_contra! h;have:=finrank_mono (show L≤R from λ Y c=>h Y c);omega
  refine⟨Y,c,?_⟩;have e:=finrank_sup_add_finrank_inf_eq R (span KD {Y});have J:Y≠0:=λ h=>s (h ▸ R.zero_mem);rw[(disjoint_span_singleton.2 λ h=>absurd h s).eq_bot,finrank_bot,finrank_span_singleton J] at e;omega
 have⟨g,m,h1⟩:=q _ l (by omega);have p:zh L 0⊔zC L 0⊔span KD {g}≤L:=sup_le l ((span_singleton_le_iff_mem _ _).2 m);have⟨o,n,h2⟩:=q _ p (by omega);have F:L≤zh L 0⊔zC L 0⊔span KD {g}⊔span KD {o}:=(eq_of_le_of_finrank_le (sup_le p ((span_singleton_le_iff_mem _ _).2 n)) (by omega)).symm.le;refine⟨yT o,yW g,λ M hM h0=>?_⟩;have hβ:∀ x y,jd M x y=zE M x y:=λ _ _=>rfl;have f:∀ Y∈L,jd M (yT Y) (yW Y)=0:=hM;have t:∀ Y∈L,∀ Z∈L,jd M (yT Z) (yW Y) = -jd M (yT Y) (yW Z):=λ Y c Z d=>by have e:=f _ (L.add_mem c d);have e1:=f Y c;have e2:=f Z d;simp only[map_add,LinearMap.add_apply] at e;grind
 have z:∀ Y∈zh L 0⊔zC L 0,∀ Z∈L,jd M (yT Z) (yW Y)=0/\jd M (yT Y) (yW Z)=0:=by
  intro Y c Z d;obtain⟨A,K,B,N,rfl⟩:=Submodule.mem_sup.1 c;have O:∀ j,A (0,j)=0:=λ j=>congrFun (mem_ker.1 K.2) j;have P:∀ i,B (i,0)=0:=λ i=>congrFun (mem_ker.1 N.2) i;have Q:yT A=0:=funext λ k=>by simp[qw,O]
  have S:yW B=0:=funext λ k=>by simp[qn,P]
  have e1:jd M (yT Z) (yW A)=0:=by rw[t A K.1 Z d,Q];simp
  have e2:jd M (yT B) (yW Z)=0:=by have:=t B N.1 Z d;rw[S,map_zero] at this;linear_combination this
  grind
 have C:∀ Y∈L,∃ r∈zh L 0⊔zC L 0,∃ a b:KD,Y=r+a•g+b•o:=by intro Y c;obtain⟨u,hu,w,hw,rfl⟩:=Submodule.mem_sup.1 (F c);obtain⟨r,D,v,hv,rfl⟩:=Submodule.mem_sup.1 hu;obtain⟨a,rfl⟩:=mem_span_singleton.1 hv;obtain⟨b,rfl⟩:=mem_span_singleton.1 hw;grind
 have T:jd M (yT g) (yW o)=0:=by grind
 have G:∀ Y∈L,∀ Z∈L,jd M (yT Z) (yW Y)=0:=by intro Y c Z d;obtain⟨r,D,a,b,rfl⟩:=C Y c;obtain⟨r2,E,a2,b2,rfl⟩:=C Z d;have H:=z r D;have U:=z r2 E;simp only[map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,(H _ (l E)).1,(H _ m).1,(H _ n).1,(U _ m).2,(U _ n).2,f g m,f o n,T,show jd M (yT o) (yW g)=0 from h0];ring
 funext a b;have⟨Y,c,hy⟩:=qX V hc (Pi.single a 1);have⟨Z,d,hx⟩:=qz V X (Pi.single b 1);have:=G Y c Z d;rw[hx,hy,hβ,xL] at this;exact this
lemma xU (f:finrank KD L=6) (g:finrank KD (L.map (z9 0))=3) (e:finrank KD (zm L 0 0)=2) (h:∀ H∈zh L 0,zB H=0):False:=by
 have d:zh L 0≤zm L 0 0:=λ H b=>by have c:∀ j,H (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 b.2) j;refine yc b.1 c λ i=>?_;refine cases (c 0) (λ a=>?_) i;have:=congrFun (h H b) a;rw[qn,c 0,sub_zero] at this;exact this
 have:=finrank_mono d;rw[y5 f g,e] at this;omega
lemma jv (A B:zx):zp A B=zp B A:=by funext i j;simp only[zR];ring
lemma Pw (A:zx):zp A A=2•zn A:=by funext i j;simp only[zR,zK,Pi.smul_apply];ring
lemma vB (A B:zx) (s t:KD):zn (s•A+t•B)=(s^2)•zn A+(s*t)•zp A B+(t^2)•zn B:=by funext i j;simp only[zR,zK,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
lemma xV (A B C:zx) (s:KD):zp A (B+s•C)=zp A B+s•zp A C:=by funext i j;simp only[zR,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
lemma Px (A:zx):zn (λ a b=>A b a)=λ a b=>zn A b a:=by funext i j;fin_cases i<;>fin_cases j<;>simp[zK,z6]<;>ring
lemma Py (A B:zx):zp (λ a b=>A b a) (λ a b=>B b a)=λ a b=>zp A B b a:=by funext i j;fin_cases i<;>fin_cases j<;>simp[zR,z6]<;>ring
lemma jB (A U:zx) {r0 c0 i1 i2 j1 j2:Fin 3} (hI:(z6 r0 0=i1/\z6 r0 1=i2)\/(z6 r0 0=i2/\z6 r0 1=i1)) (hJ:(z6 c0 0=j1/\z6 c0 1=j2)\/(z6 c0 0=j2/\z6 c0 1=j1)) (h0r:∀ c,U r0 c=0) (h0c:∀ r,U r c0=0):zp A U r0 c0=U i2 j2*A i1 j1+U i2 j1*A i1 j2+U i1 j2*A i2 j1+U i1 j1*A i2 j2/\zp A U r0 j1=U i1 j2*A i2 c0+U i2 j2*A i1 c0/\zp A U r0 j2=U i1 j1*A i2 c0+U i2 j1*A i1 c0/\zp A U i1 c0=U i2 j2*A r0 j1+U i2 j1*A r0 j2/\zp A U i2 c0=U i1 j2*A r0 j1+U i1 j1*A r0 j2/\zp A U i1 j1=U i2 j2*A r0 c0/\zp A U i1 j2=U i2 j1*A r0 c0/\zp A U i2 j1=U i1 j2*A r0 c0/\zp A U i2 j2=U i1 j1*A r0 c0:=by
 rcases hI with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>rcases hJ with⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
 fin_cases r0<;>fin_cases c0<;>simp at h0r h0c<;>refine⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩<;>simp[zR,z6,h0r,h0c]<;>ring
lemma j9 (A S:zx) (r:Fin 3) (h1:∀ c,S (z6 r 0) c=0) (h2:∀ c,S (z6 r 1) c=0):(∀ b,zp A S r b=0)/\(∀ j,zp A S (z6 r 0) j=S r (z6 j 0)*A (z6 r 1) (z6 j 1)+S r (z6 j 1)*A (z6 r 1) (z6 j 0))/\(∀ j,zp A S (z6 r 1) j=S r (z6 j 0)*A (z6 r 0) (z6 j 1)+S r (z6 j 1)*A (z6 r 0) (z6 j 0)):=by
 refine⟨λ b=>?_,λ j=>?_,λ j=>?_⟩ <;>
 fin_cases r<;>simp[z6] at h1 h2<;>first|(fin_cases b<;>simp[zR,z6,h1,h2])|(fin_cases j<;>simp[zR,z6,h1,h2]<;>ring)
lemma kx (V:zx) (r0 c0:Fin 3) (h0r:∀ c,V r0 c=0) (h0c:∀ r,V r c0=0):∀ a,a≠r0->∀ b,zn V a b=0:=by intro a d b;fin_cases r0<;>fin_cases c0<;>simp at h0r h0c<;>fin_cases a<;>simp at d<;>fin_cases b<;>simp[zK,z6,h0r,h0c]
open LinearMap in
lemma kX (U:Submodule KD (Fin 3->KD)) (h:∀ x∈U,x 0*(-x 0-x 1-x 2)+x 1*x 2=0):finrank KD U≤1:=by
 let B:(Fin 3->KD) →ₗ[KD] (Fin 3->KD) →ₗ[KD] KD:=mk₂ KD (λ x y=>-2*x 0*y 0-x 0*y 1-x 1*y 0-x 0*y 2-x 2*y 0+x 1*y 2+x 2*y 1) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring) (by intros;simp;ring);have b:∀ x y,B x y=B y x:=λ x y=>by simp[B];ring
 have c:=yr B b U λ x a=>by simp[B];linear_combination 2*h x a
 have d:U⊓ker B=⊥:=(Submodule.eq_bot_iff _).2 λ x a=>by
  have e:=λ y=>LinearMap.congr_fun (mem_ker.1 (Submodule.mem_inf.1 a).2) y;have f:=e (Pi.single 0 1);have g:=e (Pi.single 1 1);have j:=e (Pi.single 2 1);simp[B] at f g j;have k:x 0=0:=by grind
  have l:x 1=0:=by grind
  have m:x 2=0:=by grind
  funext i;fin_cases i;exacts[k,l,m]
 have:=qr B U U c;rw[d,finrank_bot] at this;simp at this;omega
def qM (T:zx) (r0 c0:Fin 3):Prop :=
 (∀ c,T r0 c=0)/\(∀ r,T r c0=0)/\(∀ r,r≠r0->∀ c,c≠c0 -> T r c≠0)
def jK (N:Submodule KD zx) (P:zx -> Prop):Prop :=
 finrank KD N=2 /\
 (∀ A∈N,P (zn A)/\(∑ a,∑ b,A a b=0)/\zo A=0) /\
 (∀ M M' (c:KD),P M -> P M' -> P (M+c•M')) /\
 (∀ M,P M->(∀ a a' b b',M a b*M a' b'=M a b'*M a' b) -> M=0) /\
 (∃ x y:Fin 3->KD,∀ M,P M -> zE M x y=0 -> M=0) /\
 (∃ y:Fin 3->KD,y≠0/\∀ M,P M->∀ b,∑ a,y a*M a b=0) /\
 (∀ r,¬ ∀ A∈N,∀ i,i≠r->∀ j,A i j=0) /\
 (∀ T∈N,∀ S∈N,∀ r0 c0:Fin 3,qM T r0 c0 -> zn T=0 ->
  (∀ i,i≠r0->∀ c,S i c=0) -> S r0 c0≠0 -> zn S=0 -> zp T S≠0 -> False)
lemma vC {N:Submodule KD zx} {P:zx -> Prop} (h:jK N P) {A B:zx} (a:A∈N) (b:B∈N):P (zp A B):=by
 have e:zp A B=zn (A+B)+(-1:KD)•zn A+(-1:KD)•zn B:=by funext i j;simp only[zp,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
 rw[e];exact h.2.2.1 _ _ _ (h.2.2.1 _ _ _ (h.2.1 _ (N.add_mem a b)).1 (h.2.1 A a).1) (h.2.1 B b).1
lemma Pz {N:Submodule KD zx} {P:zx -> Prop} (h:jK N P):∃ T∈N,T≠0/\zn T=0:=by
 obtain⟨b,n,-,-,⟨x,y,o⟩,-⟩:=h;have⟨A,g,c⟩:=exists_mem_ne_zero_of_ne_bot (p:=N) (λ d=>by rw[d,finrank_bot] at b;omega);have⟨B,a,i⟩:∃ B∈N,B∉span KD {A}:=by by_contra! j;have:=finrank_mono (show N≤span KD {A} from λ B a=>j B a);rw[b,finrank_span_singleton c] at this;omega
 have⟨s,t,k,l⟩:=vv (zE (zn A) x y) (zE (zp A B) x y) (zE (zn B) x y);refine⟨s•A+t•B,N.add_mem (N.smul_mem s g) (N.smul_mem t a),λ e=>?_,o _ (n _ (N.add_mem (N.smul_mem s g) (N.smul_mem t a))).1 ?_⟩
 . by_cases f:t=0
   . rw[f,zero_smul,add_zero] at e;exact k.elim (λ q=>c ((smul_eq_zero.1 e).resolve_left q)) (λ d=>d f)
   . have m:t•B = -(s•A):=eq_neg_of_add_eq_zero_right e;refine i (mem_span_singleton.2 ⟨-s/t,?_⟩);rw[show B=t⁻¹•(t•B) by rw[smul_smul,inv_mul_cancel₀ f,one_smul],m,smul_neg,smul_smul,←neg_smul];congr 1;ring
 . rw[vB];simp only[zE,Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_univ_three] at l⊢;linear_combination l
lemma xW {N:Submodule KD zx} {P:zx -> Prop} (h:jK N P) {T V:zx} (f:T∈N) (b:zn T=0) (g:V∈N) (c:zp T V≠0):∃ S∈N,S≠0/\zn S=0/\zp T S≠0:=by
 have p:=vC h f g;obtain⟨-,k,l,-,⟨x,y,m⟩,-⟩:=h;have o:zE (zp T V) x y≠0:=by grind
 set κ:=zE (zn V) x y/zE (zp T V) x y;have d:V+(-κ)•T∈N:=N.add_mem g (N.smul_mem _ f);have a:zp T (V+(-κ)•T)=zp T V:=by rw[xV,Pw,b];simp
 refine⟨V+(-κ)•T,d,λ n=>c ?_,m _ (k _ d).1 ?_,by rw[a];exact c⟩
 . rw[←a,n];funext i j;simp[zR]
 . have e:zn (V+(-κ)•T)=zn V+(-κ)•zp T V:=by
    rw[show V+(-κ)•T=(1:KD)•V+(-κ)•T by simp,vB,b,jv];simp
   rw[e,vA];simp only[κ];field_simp;ring
lemma zO {r:Fin 3} (x:Fin 3):x=r\/x=z6 r 0\/x=z6 r 1:=by revert x r;decide
open LinearMap in
lemma xX {N:Submodule KD zx} {U:zx} {r0 d:Fin 3} (P:2≤finrank KD N) (L:qM U r0 d) (F:zn U=0) (t:∀ V∈N,zp V U=0) (G:∀ V∈N,(∀ a a' b b',zn V a b*zn V a' b'=zn V a b'*zn V a' b) -> zn V=0) (M:∀ V∈N,∑ a,∑ b,V a b=0):False:=by
 have⟨w,y,O⟩:=L;have⟨Q,R,S⟩:=zN r0;have⟨T,W,X⟩:=zN d;have Y:U (zV r0 0) (zV d 0)*U (zV r0 1) (zV d 1)+U (zV r0 0) (zV d 1)*U (zV r0 1) (zV d 0)=0:=by have:=congrFun (congrFun F r0) d;rwa[zK] at this
 have z:U (zV r0 1) (zV d 1)*U (zV r0 0) (zV d 0)-U (zV r0 0) (zV d 1)*U (zV r0 1) (zV d 0)≠0:=by grind
 have g:∀ V∈N,(∀ c,V r0 c=0)/\∀ r,V r d=0:=λ V e=>by
  obtain⟨H,A,B,C,D,I,-,-,-⟩:=jB V U (Or.inl ⟨rfl,rfl⟩) (Or.inl ⟨rfl,rfl⟩) w y;simp only[t V e,Pi.zero_apply] at H A B C D I;have⟨Z,a2⟩:=jn (u:=V (zV r0 0) d) (v:=V (zV r0 1) d) z (by linear_combination -A) (by linear_combination -B);have⟨b1,b2⟩:=jn (u:=V r0 (zV d 0)) (v:=V r0 (zV d 1)) (show U (zV r0 1) (zV d 1)*U (zV r0 0) (zV d 0)-U (zV r0 1) (zV d 0)*U (zV r0 0) (zV d 1)≠0 by
   rw[mul_comm (U (zV r0 1) (zV d 0))];exact z)
   (by linear_combination -C) (by linear_combination -D)
  have b0:V r0 d=0:=by grind
  exact⟨λ c=>by rcases zO (r:=d) c with rfl|rfl|rfl<;>assumption,λ r=>by rcases zO (r:=r0) r with rfl|rfl|rfl<;>assumption⟩
 have k:∀ V∈N,V (zV r0 0) (zV d 0)*V (zV r0 1) (zV d 1)+V (zV r0 0) (zV d 1)*V (zV r0 1) (zV d 0)=0:=λ V e=>by have⟨h,f⟩:=g V e;have J:=G V e (qV r0 (kx V r0 d h f));have:=congrFun (congrFun J r0) d;rwa[zK] at this
 set ψ:zx →ₗ[KD] (Fin 3->KD):=LinearMap.pi ![yj (zV r0 0) (zV d 0),yj (zV r0 0) (zV d 1),yj (zV r0 1) (zV d 0)];have i:∀ V∈N,V (zV r0 1) (zV d 1) = -(V (zV r0 0) (zV d 0)+V (zV r0 0) (zV d 1)+V (zV r0 1) (zV d 0)):=λ V e=>by have⟨h,f⟩:=g V e;have:=M V e;rw[qU _ r0] at this;simp only[qU _ d,h,f] at this;linear_combination this
 have l:N⊓ker ψ=⊥:=by
  rw[eq_bot_iff];intro V e;have⟨j,E⟩:=Submodule.mem_inf.1 e;have m:=mem_ker.1 E;have n:=congrFun m 0;have o:=congrFun m 1;have p:=congrFun m 2;simp only[ψ,pi_apply,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons,yp,Pi.zero_apply] at n o p;have q:=i V j;rw[n,o,p] at q;simp at q;have⟨h,f⟩:=g V j;rw[mem_bot];funext a b;rcases zO (r:=r0) a with rfl|rfl|rfl
  . exact h b
  . rcases zO (r:=d) b with rfl|rfl|rfl
    exacts[f _,n,o]
  . rcases zO (r:=d) b with rfl|rfl|rfl
    exacts[f _,p,q]
 have s:=zW ψ N;rw[l,finrank_bot,add_zero] at s;have:=kX (N.map ψ) (λ x K=>by obtain⟨V,e,rfl⟩:=K;simp only[ψ,pi_apply,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons,yp];have:=k V e;rw[i V e] at this;linear_combination this);omega
lemma PA {N:Submodule KD zx} {P:zx -> Prop} (h:jK N P) {U:zx} {r0 d:Fin 3} (e:qM U r0 d) (c:zn U=0) (b:∀ V∈N,zp U V=0):False:=xX h.1.ge e c (λ V a=>by rw[jv];exact b V a) (λ V a=>h.2.2.2.1 _ (h.2.1 V a).1) λ V a=>(h.2.1 V a).2.1
lemma xY:∀ r0 r1:Fin 3,r1≠r0->∃ i2,(z6 r0 0=r1/\z6 r0 1=i2)\/(z6 r0 0=i2/\z6 r0 1=r1):=by decide
lemma PB {r0 a b:Fin 3} (c:(z6 r0 0=a/\z6 r0 1=b)\/(z6 r0 0=b/\z6 r0 1=a)) (f:Fin 3->KD):∑ k,f k=f r0+f a+f b:=by rw[qU f r0];rcases c with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>ring
lemma PC {r0 a b:Fin 3} (c:(z6 r0 0=a/\z6 r0 1=b)\/(z6 r0 0=b/\z6 r0 1=a)) (x:Fin 3):x=r0\/x=a\/x=b:=by rcases c with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>rcases zO (r:=r0) x with h|h|h<;>simp[h]
lemma vD {N:Submodule KD zx} {P:zx -> Prop} (h:jK N P) {U S:zx} (hU:U∈N) {r0 d:Fin 3} (z:qM U r0 d) (Q:zn U=0) (hS:S∈N) (R:zn S=0) (A:zp U S≠0) (a4:(∃ r1 c1,qM S r1 c1)\/∃ r,∀ i,i≠r->∀ c,S i c=0):False:=by
 have e:=vC h hU hS;obtain⟨-,-,-,l,-,⟨y,T,B⟩,-,V⟩:=h;have a0:=z;have⟨m,n,J⟩:=z;rw[jv] at A e;have⟨s1,s2,s3⟩:=zN r0;have⟨t1,t2,t3⟩:=zN d;rcases a4 with⟨r1,c1,C,D,K⟩|⟨r,W⟩
 . by_cases o:r1=r0
   . subst o
     obtain⟨-,-,-,X,Y,q,s,t,w⟩:=jB S U (Or.inl ⟨rfl,rfl⟩) (Or.inl ⟨rfl,rfl⟩) m n;refine A (l _ e (qV r1 λ a ha b=>?_));rcases zO (r:=r1) a with rfl|rfl|rfl
     . exact absurd rfl ha
     . rcases zO (r:=d) b with rfl|rfl|rfl<;>simp[X,q,s,C]
     . rcases zO (r:=d) b with rfl|rfl|rfl<;>simp[Y,t,w,C]
   by_cases p:c1=d
   . subst p
     obtain⟨-,H,I,-,-,q,s,t,w⟩:=jB S U (Or.inl ⟨rfl,rfl⟩) (Or.inl ⟨rfl,rfl⟩) m n;refine A (l _ e (jo c1 λ b z a=>?_));rcases zO (r:=c1) b with rfl|rfl|rfl
     . exact absurd rfl z
     . rcases zO (r:=r0) a with rfl|rfl|rfl<;>simp[H,q,t,D]
     . rcases zO (r:=r0) a with rfl|rfl|rfl<;>simp[I,s,w,D]
   have⟨f,Z⟩:=xY r0 r1 o;have⟨g,hJ⟩:=xY d c1 p;have L:r1≠f:=by grind
   have M:c1≠g:=by grind
   have E:f≠r0:=by grind
   have F:g≠d:=by grind
   have⟨g1,H,I,X,Y,q,s,t,w⟩:=jB S U Z hJ m n;have pU:=j6 Q L M;have pS:=j6 R (Ne.symm E) (Ne.symm F);have nb:=J r1 (Ne.symm o |>.symm) c1 p;have ne:=J f E g F;have O:=K r0 (Ne.symm o) d (Ne.symm p);have a5:=K f (Ne.symm L) g (Ne.symm M);have G:=B _ e d;have j:=B _ e c1;have k:=B _ e g;rw[PB Z] at G j k;rw[g1,X,Y] at G;rw[H,q,t] at j;rw[I,s,w] at k;simp only[C,D,mul_zero,add_zero,zero_add] at G j k;have a1:y r0=0:=by grind
   rw[a1] at j k;simp only[zero_mul,zero_add] at j k;have⟨a6,a7⟩:=jn (u:=y r1) (v:=y f) (show U f g*U r1 c1-U r1 g*U f c1≠0 by
    rw[show U f g*U r1 c1-U r1 g*U f c1=2*(U r1 c1*U f g) by linear_combination -pU];exact mul_ne_zero two_ne_zero (mul_ne_zero nb ne))
    (mul_left_cancel₀ O (by linear_combination j)) (mul_left_cancel₀ O (by linear_combination k))
   exact T (funext λ x=>by rcases PC Z x with rfl|rfl|rfl<;>assumption)
 . have⟨q1,q2,q3⟩:=zN r
   by_cases a2:r=r0
   . subst a2
     by_cases a3:S r d=0
     . obtain⟨-,H,I,-,-,q,s,t,w⟩:=jB S U (Or.inl ⟨rfl,rfl⟩) (Or.inl ⟨rfl,rfl⟩) m n
       refine A (l _ e (jo d λ b z a=>?_));rcases zO (r:=d) b with rfl|rfl|rfl
       . exact absurd rfl z
       . rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
       . rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
     . exact V U hU S hS r d a0 Q W a3 R (by rw[jv];exact A)
   . have⟨z0,z1,z2⟩:=j9 U S r (W _ (Ne.symm q1)) (W _ (Ne.symm q2));refine A (l _ e (qV r0 λ a ha b=>?_));rw[jv];rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
lemma vE:∀ k:Fin 3,(z6 (z6 k 0) 0=k/\z6 (z6 k 0) 1=z6 k 1)\/(z6 (z6 k 0) 0=z6 k 1/\z6 (z6 k 0) 1=k):=by decide
lemma jR (p v:Fin 3->KD) (hQ:∀ j,p (z6 j 0)*v (z6 j 1)+p (z6 j 1)*v (z6 j 0)=0) (hps:∑ c,p c=0) (hp0:p≠0) (hv:v≠0):∃ k0,p k0=0/\p (z6 k0 0)≠0:=by
 by_contra! f;have a:∀ k,p k≠0:=λ k g=>by
  have h:=f k g;have l:p (z6 k 1)=0:=by have:=hps;rw[qU p k,g,h] at this;simpa using this
  apply hp0;funext i;rcases zO (r:=k) i with rfl|rfl|rfl<;>assumption
 have b:=hQ 0;have d:=hQ 1;have e:=hQ 2;simp only[z6,cons_val_zero,cons_val_one,cons_val_two,head_cons,Matrix.tail_cons] at b d e;have m:=(mul_eq_zero.1 (show 2*p 1*p 2*v 0=0 by
  linear_combination p 1*d+p 2*e-p 0*b)).resolve_left
  (mul_ne_zero (mul_ne_zero two_ne_zero (a 1)) (a 2))
 have n:=(mul_eq_zero.1 (show 2*p 0*p 2*v 1=0 by
  linear_combination p 0*b+p 2*e-p 1*d)).resolve_left
  (mul_ne_zero (mul_ne_zero two_ne_zero (a 0)) (a 2))
 have o:=(mul_eq_zero.1 (show 2*p 0*p 1*v 2=0 by
  linear_combination p 0*b+p 1*d-p 2*e)).resolve_left
  (mul_ne_zero (mul_ne_zero two_ne_zero (a 0)) (a 1))
 exact hv (funext λ i=>by fin_cases i<;>simpa)
lemma jq (p v:Fin 3->KD) (k0:Fin 3) (hQ:∀ j,p (z6 j 0)*v (z6 j 1)+p (z6 j 1)*v (z6 j 0)=0) (hps:∑ c,p c=0) (hpk:p k0=0) (hp1:p (z6 k0 0)≠0):v k0=0/\v (z6 k0 0)=v (z6 k0 1):=by
 have f:p (zV k0 0)+p (zV k0 1)=0:=by have:=hps;rw[qU p k0,hpk] at this;linear_combination this
 have e:p (zV k0 1)≠0:=by grind
 have g:=hQ k0;have d:=hQ (zV k0 0);refine⟨?_,?_⟩
 . rcases vE k0 with⟨a,b⟩|⟨a,b⟩<;>rw[a,b,hpk] at d<;>grind
 grind
lemma PD (T S:zx) (r c:Fin 3) (f:∀ x,T (z6 r 0) x=0) (g:∀ x,T (z6 r 1) x=0) (n:∀ b,b≠c->∀ a,S a b=0):∀ a a' b b',zp S T a b*zp S T a' b'=zp S T a b'*zp S T a' b:=by
 have⟨i,j,k⟩:=j9 S T r f g;have h:∀ a x,S a x=(if x=c then 1 else 0)*S a c:=λ a x=>by grind
 have l:∀ b,zp S T (zV r 0) b=(T r (zV b 0)*(if zV b 1=c then 1 else 0)+T r (zV b 1)*(if zV b 0=c then 1 else 0))*S (zV r 1) c:=λ b=>by grind
 have m:∀ b,zp S T (zV r 1) b=(T r (zV b 0)*(if zV b 1=c then 1 else 0)+T r (zV b 1)*(if zV b 0=c then 1 else 0))*S (zV r 0) c:=λ b=>by grind
 intro a a' b b';rcases zO (r:=r) a with e|e|e<;>rcases zO (r:=r) a' with d|d|d<;>grind
lemma kO (V:zx) (r k0:Fin 3) (h1:V (z6 r 0) k0=0) (h2:V (z6 r 1) k0=0) (h3:V (z6 r 0) (z6 k0 0)=V (z6 r 0) (z6 k0 1)) (h4:V (z6 r 1) (z6 k0 0)=V (z6 r 1) (z6 k0 1)):zo V=2*V r k0*V (z6 r 0) (z6 k0 1)*V (z6 r 1) (z6 k0 1)/\(∀ b,b≠k0 -> zn V r b=0)/\zn V r k0=2*V (z6 r 0) (z6 k0 1)*V (z6 r 1) (z6 k0 1)/\(∀ b,b≠k0 -> zn V (z6 r 0) b=V r k0*V (z6 r 1) (z6 k0 1))/\(∀ b,b≠k0 -> zn V (z6 r 1) b=V r k0*V (z6 r 0) (z6 k0 1))/\zn V (z6 r 0) k0=(V r (z6 k0 0)+V r (z6 k0 1))*V (z6 r 1) (z6 k0 1)/\zn V (z6 r 1) k0=(V r (z6 k0 0)+V r (z6 k0 1))*V (z6 r 0) (z6 k0 1):=by fin_cases r<;>fin_cases k0<;>simp[z6] at h1 h2 h3 h4⊢<;>refine⟨?_,λ b a=>?_,?_,λ b a=>?_,λ b a=>?_,?_,?_⟩<;>(try fin_cases b)<;>simp_all[zs,zK,z6]<;>ring
lemma xZ {N:Submodule KD zx} {P:zx -> Prop} (h:jK N P) (D:∀ V∈N,V≠0 -> zn V=0->∀ r0 c0,¬ qM V r0 c0) {T:zx} (H:T∈N) (a5:T≠0) (a6:zn T=0) {r:Fin 3} (E:∀ i,i≠r->∀ c,T i c=0):False:=by
 have⟨q1,q2,q3⟩:=zN r;have l:∀ x,T (zV r 0) x=0:=E _ (q1.symm);have m:∀ x,T (zV r 1) x=0:=E _ (q2.symm);have n:∑ c,T r c=0:=by have:=(h.2.1 T H).2.1;rw[qU _ r] at this;simpa[l,m] using this
 have I:(λ c=>T r c)≠0:=λ k=>a5 (funext λ i=>funext λ c=>by
  rcases zO (r:=r) i with rfl|rfl|rfl
  exacts[congrFun k c,l c,m c])
 have v:=h.2.2.2.1;by_cases t:∀ V∈N,zp T V=0
 . have F:∀ V∈N,(∀ j,T r (zV j 0)*V (zV r 1) (zV j 1)+T r (zV j 1)*V (zV r 1) (zV j 0)=0)/\(∀ j,T r (zV j 0)*V (zV r 0) (zV j 1)+T r (zV j 1)*V (zV r 0) (zV j 0)=0):=λ V g=>by
    obtain⟨-,Y,Z⟩:=j9 V T r l m;have e:=t V g;rw[jv] at e;exact⟨λ j=>by rw[←Y,e];rfl,λ j=>by rw[←Z,e];rfl⟩
   by_cases u:∀ V∈N,∀ i,i≠r->∀ j,V i j=0
   . exact h.2.2.2.2.2.2.1 r u
   push Not at u;have⟨V,g,i,R,j,f⟩:=u;have⟨d,w,y⟩:∃ d,T r d=0/\T r (zV d 0)≠0:=by
    rcases zO (r:=r) i with rfl|rfl|rfl
    . exact absurd rfl R
    . exact jR (λ c=>T r c) _ (F V g).2 n I λ k=>f (congrFun k j)
    . exact jR (λ c=>T r c) _ (F V g).1 n I λ k=>f (congrFun k j)
   have b0:T r (zV d 1)≠0:=λ h'=>by have:=n;rw[qU _ d,w,h'] at this;exact y (by simpa using this)
   have⟨w1,w2⟩:=jq (λ c=>T r c) _ d (F V g).2 n w y;have⟨w3,w4⟩:=jq (λ c=>T r c) _ d (F V g).1 n w y;have⟨u1,u2,u3⟩:=zN d;have⟨a7,b1⟩:V i d=0/\V i (zV d 0)=V i (zV d 1):=by grind
   have J:V≠0:=λ k=>f (by rw[k];rfl);by_cases z:zn V=0
   . rcases qd V J z with⟨U,A⟩|⟨W,B⟩|⟨r0,c0,o,p,q,-,-⟩
     . have a0:i=U:=by by_contra C;exact f (A i C j)
       subst a0;have hW:T+V∈N:=N.add_mem H g;have K:zn (T+V)=0:=by have:=vB T V 1 1;simp only[one_smul,one_pow,one_mul] at this;grind
       have b2:∀ x,(T+V) r x=T r x:=λ x=>by simp[A r (R.symm)]
       have a1:(T+V) i j=V i j:=by simp[E i R]
       have L:T+V≠0:=λ k=>f (by rw[←a1,k];rfl);rcases qd _ L K with⟨a2,a8⟩|⟨a3,a9⟩|⟨r0,c0,o,p,q,-,-⟩
       . have:a2=r:=by
          grind
         grind
       . have e1:zV d 0=a3:=by
          grind
         grind
       . exact D _ hW L K r0 c0 ⟨o,p,q⟩
     . have b3:j=W:=by by_contra C;exact f (B j C i)
       rcases zO (r:=d) j with hj|hj|hj<;>grind
     . exact D V g J z r0 c0 ⟨o,p,q⟩
   . have⟨e0,e1,e2,e3,e4,e5,e6⟩:=kO V r d w1 w3 w2 w4
     have s:=(h.2.1 V g).2.2;rw[e0] at s;refine z (v _ (h.2.1 V g).1 ?_);rcases mul_eq_zero.1 s with s|s
     . rcases mul_eq_zero.1 s with s|s
       . have b4:V r d=0:=(mul_eq_zero.1 s).resolve_left two_ne_zero;refine jo d λ b hb a=>?_;rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
       . refine qV (zV r 0) λ a G b=>?_
         grind
     . refine qV (zV r 1) λ a G b=>?_
       grind
 . push Not at t
   have⟨V,g,a4⟩:=t;have⟨S,hS,M,O,X⟩:=xW h H a6 g a4;have Q:=vC h hS H;rw[jv] at X;rcases qd S M O with⟨U,A⟩|⟨W,B⟩|⟨r0,c0,o,p,q,-,-⟩
   . have⟨z0,Y,Z⟩:=j9 S T r l m
     refine X (v _ Q ?_);rcases zO (r:=r) U with hr|hr|hr
     . refine qV r λ a G b=>?_
       grind
     . refine qV (zV r 1) λ a G b=>?_
       rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
     . refine qV (zV r 0) λ a G b=>?_
       rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
   . exact X (v _ Q (PD T S r W l m B))
   . exact D S hS M O r0 c0 ⟨o,p,q⟩
lemma Z0 {U:zx} {r0 d:Fin 3} (h:qM U r0 d):qM (λ a b=>U b a) d r0:=⟨λ c=>h.2.1 c,λ r=>h.1 r,λ r e c f=>h.2.2 c f r e⟩
lemma vF {A:zx} (h:A≠0):(λ a b=>A b a)≠0:=λ c=>h (funext λ a=>funext λ b=>congrFun (congrFun c b) a)
lemma kP {A:zx} (h:zn A=0):zn (λ a b=>A b a)=0:=by rw[Px,h];rfl
lemma PE {N D:Submodule KD zx} {P K:zx -> Prop} (h:jK N P) (G:jK D K) (H:∀ A,A∈D↔(λ a b=>A b a)∈N):False:=by
 have u:∀ A∈N,(λ a b=>A b a)∈D:=by grind
 have⟨T,v,j,k⟩:=Pz h;by_cases n:∃ U∈N,U≠0/\zn U=0/\∃ d e,qM U d e
 . obtain⟨U,t,-,f,d,e,l⟩:=n
   by_cases g:∀ V∈N,zp U V=0
   . exact PA h l f g
   push Not at g;have⟨V,o,E⟩:=g;have⟨S,w,F,m,x⟩:=xW h t f o E;rcases qd S F m with y|⟨c,z⟩|⟨I,J,a,b,c,-,-⟩
   . exact vD h t l f w m x (Or.inr y)
   . refine vD G (u U t) (Z0 l) (kP f) (u S w) (kP m) ?_ (Or.inr ⟨c,λ i B C=>z i B C⟩);rw[Py];exact vF x
   . exact vD h t l f w m x (Or.inl ⟨I,J,a,b,c⟩)
 . push Not at n
   rcases qd T j k with⟨r,y⟩|⟨c,z⟩|⟨d,e,a,b,c,-,-⟩
   . exact xZ h (λ V o p q d e s=>n V o p q d e s) v j k y
   . refine xZ G (λ V o p q d e s=>n _ ((H V).1 o) (vF p) (kP q) e d (Z0 s)) (u T v) (vF j) (kP k) (r:=c) (λ i B C=>z i B C)
   . exact n T v j k d e ⟨a,b,c⟩
def yx:Prop :=
 ∀ L:Submodule KD ze,zg L -> finrank KD L=6 -> finrank KD (L.map (z9 0))=3 ->
  ∀ i' i'':Fin 4,i'≠0 -> i''≠0 -> i'≠i'' ->
   finrank KD ((zh L 0).map (z9 i'))≤1 ->
   finrank KD ((zh L 0).map (z9 i''))≤1 -> False
open LinearMap in
lemma jC (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) {W:Submodule KD ze} (hW:W≤zh L 0) (hW2:2≤finrank KD W) (ρ:Fin 4) (hρ:∀ X∈W,∀ j,X (ρ,j)=0):finrank KD ((zh L 0).map (z9 ρ))≤1:=by have e:=zW (z9 ρ) (zh L 0);have a:W≤zh L 0⊓ker (z9 ρ):=λ X b=>Submodule.mem_inf.2 ⟨hW b,mem_ker.2 (funext (hρ X b))⟩;have:=finrank_mono a;rw[y5 h6 hr] at e;omega
lemma jS (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hF3:yx) {W:Submodule KD ze} (hW:W≤zh L 0) (hW2:2≤finrank KD W) {r0:Fin 3} (hρ:∀ X∈W,∀ i,i≠r0->∀ j,X (i.succ,j)=0):False:=hF3 L hL h6 hr _ _ (succ_ne_zero _) (succ_ne_zero _) (λ h=>(zN r0).2.2 (succ_injective _ h)) (jC h6 hr hW hW2 _ λ X a=>hρ X a _ (Ne.symm (zN r0).1)) (jC h6 hr hW hW2 _ λ X a=>hρ X a _ (Ne.symm (zN r0).2.1))
lemma jD (hL:zg L) {T S:ze} (hT:T∈zm L 0 0) (hS:S∈zm L 0 0):yw L (zp (z7 0 0 T) (z7 0 0 S)):=by
 have e:zp (qZ T) (qZ S)=zn (qZ (T+S))+(-1:KD)•zn (qZ T)+(-1:KD)•zn (qZ S):=by funext i j;simp only[zp,map_add,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
 rw[e];exact kN (kN (λ Y a=>(qG hL a ((zm L 0 0).add_mem hT hS)).1) (λ Y a=>(qG hL a hT).1) _) (λ Y a=>(qG hL a hS).1) _
lemma Z3:∀ k:Fin 3,(z6 (z6 k 1) 0=k/\z6 (z6 k 1) 1=z6 k 0)\/(z6 (z6 k 1) 0=z6 k 0/\z6 (z6 k 1) 1=k):=by decide
lemma PF (A B U:zx) (x y a:Fin 3->KD) (t:KD):zE (zp (A+t•B) U) x (y+t•a)=zE (zp A U) x y+t*(zE (zp B U) x y+zE (zp A U) x a)+t^2*zE (zp B U) x a:=by simp only[zE,zR,Pi.add_apply,Pi.smul_apply,smul_eq_mul,sum_univ_three];ring
lemma Z4 (M:zx) (x y:Fin 3->KD) (r0:Fin 3) (a:y (z6 r0 0)=0) (c:y (z6 r0 1)=0):zE M x y=y r0*∑ b,M r0 b*x b:=by simp only[zE];rw[qU _ r0,a,c,Finset.mul_sum];simp only[zero_mul,sum_const_zero,add_zero];grind
lemma Z5 {c:ze} (f:c∈zh L 0) {U:zx} (l:∀ Y∈L,zE (zp (zv Y) U) (zw Y) (zB Y)=0) {Y:ze} (m:Y∈L):zE (zp (zv c) U) (zw Y) (zB Y)+zE (zp (zv Y) U) (zw Y) (zB c)=0/\zE (zp (zv c) U) (zw Y) (zB c)=0:=by
 have d:∀ j,c (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 f.2) j;have g:zw c=0:=funext λ b=>by simp[qw,d]
 have h:∀ t:KD,zv (Y+t•c)=zv Y+t•zv c:=λ t=>by funext a b;simp only[zv,Pi.add_apply,Pi.smul_apply,smul_eq_mul,d];ring
 obtain⟨-,i,k⟩:=qc (zE (zp (zv Y) U) (zw Y) (zB Y)) (zE (zp (zv c) U) (zw Y) (zB Y)+zE (zp (zv Y) U) (zw Y) (zB c)) (zE (zp (zv c) U) (zw Y) (zB c)) λ t=>by have e:=l _ (L.add_mem m (L.smul_mem t f.1));rw[h,map_add,map_add,map_smul,map_smul,g,smul_zero,add_zero,PF] at e;linear_combination e
 exact⟨i,k⟩
lemma Z6 (c A:zx) (r0 a i:Fin 3) (n:c r0 a≠0) (h:A i a=0) (k:∀ j,c r0 (z6 j 0)*A i (z6 j 1)+c r0 (z6 j 1)*A i (z6 j 0)=0):∀ b,A i b=0:=λ b=>by
 have l:=k (zV a 0);have m:=k (zV a 1);rcases vE a with⟨d,e⟩|⟨d,e⟩<;>rw[d,e,h] at l <;>
 rcases Z3 a with⟨f,g⟩|⟨f,g⟩<;>rw[f,g,h] at m <;>
 rcases zO (r:=a) b with rfl|rfl|rfl <;>
 grind
lemma PG (E:zg L) (F:finrank KD L=6) (v:finrank KD (L.map (z9 0))=3) (w:finrank KD (zm L 0 0)=2) {d h:zx} {r0 b:Fin 3} (x:yw L (zp d h)) (I:∀ r,d r b=0) (G:d (z6 r0 1) (z6 b 1)*d (z6 r0 0) (z6 b 0)-d (z6 r0 0) (z6 b 1)*d (z6 r0 1) (z6 b 0)≠0) (l:∀ i,i≠r0->∀ c,h i c=0) (J:h r0 b≠0):∃ Yt∈zh L 0,zB Yt r0=1/\zB Yt (z6 r0 0)=0/\zB Yt (z6 r0 1)=0:=by
 obtain⟨y,z,-⟩:=zN r0;have⟨A,B,C⟩:=j9 d h r0 (l _ (y.symm)) (l _ (z.symm));have g:∀ H∈zh L 0,yW H (zV r0 0)=0/\yW H (zV r0 1)=0:=by
  intro H f;have e:=xS E v f x;have j:=e (zV b 0);have k:=e (zV b 1);rw[qU _ r0,A,B,C] at j k;rcases vE b with⟨o,p⟩|⟨o,p⟩<;>rw[o,p] at j <;>
  rcases Z3 b with⟨q,s⟩|⟨q,s⟩<;>rw[q,s] at k <;>
  grind
 have⟨H,f,t⟩:∃ H∈zh L 0,yW H≠0:=by by_contra! u;exact xU F v w u
 have m:yW H r0≠0:=λ D=>t (funext λ a=>by
  rcases zO (r:=r0) a with rfl|rfl|rfl
  exacts[D,(g H f).1,(g H f).2])
 have n:=smul_mem _ (yW H r0)⁻¹ f;refine⟨_,n,?_,(g _ n).1,(g _ n).2⟩;simp only[map_smul,Pi.smul_apply,smul_eq_mul];exact inv_mul_cancel₀ m
lemma PH (B:zg L) (C:finrank KD L=6) (D:finrank KD (L.map (z9 0))=3) (t:yx) {T S d:ze} (u:T∈zm L 0 0) (v:S∈zm L 0 0) (n:d∈zh L 0) {r0 w:Fin 3} (x:zB d r0=1) (y:∀ i,i≠r0 -> zB d i=0) (z:∀ i,i≠r0->∀ c,z7 0 0 S i c=0) (E:z7 0 0 S r0 w≠0) (κ:KD) (F:∀ i,i≠r0->∀ b,(zv d+(-κ)•z7 0 0 T) i b=0):False:=by
 have e:∀ j,d (0,j)=0:=λ j=>congrFun (LinearMap.mem_ker.1 n.2) j;have f:=(qJ u).2.2;have g:=(qJ v).2.2;set H':=d+(-κ)•T;have p:H'∈zh L 0:=(zh L 0).add_mem n ((zh L 0).smul_mem _ u.1);have o:∀ i,i≠r0->∀ j,H' (i.succ,j)=0:=λ i h j=>by
  refine cases ?_ (λ b=>?_) j
  . have:=y i h;rw[qn,e 0,sub_zero] at this;simp[H',this,f]
  . have q:=F i h b;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,zv,e 0,sub_zero,qL] at q;simp only[H',Pi.add_apply,Pi.smul_apply,smul_eq_mul];exact q
 have r:H' (r0.succ,0)=1:=by have:=x;rw[qn,e 0,sub_zero] at this;simp[H',this,f]
 have s:LinearIndependent KD ![S,H']:=by
  rw[LinearIndependent.pair_iff];intro a b l;have e1:=congrFun l (r0.succ,0);simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,g,r] at e1;have m:b=0:=by simpa using e1
  rw[m,zero_smul,add_zero] at l;have:=congrFun l (r0.succ,w.succ);simp only[←qL] at this;exact⟨(mul_eq_zero.1 this).resolve_right E,m⟩
 refine jS B C D t (W:=span KD (Set.range ![S,H'])) ?_ ?_ (r0:=r0) ?_
 . rw[span_le];rintro _ ⟨k,rfl⟩;fin_cases k;exacts[v.1,p]
 . rw[finrank_span_eq_card s];simp
 . intro X A i h j
   obtain⟨c,rfl⟩:=(mem_span_range_iff_exists_fun KD).1 A;simp only[sum_univ_two,cons_val_zero,cons_val_one,Pi.add_apply,Pi.smul_apply,smul_eq_mul,o i h j];refine cases ?_ (λ b=>?_) j
   . simp[g]
   . have:=z i h b;rw[qL] at this;simp[this]
lemma PI (g:zg L) (C:finrank KD L=6) (p:finrank KD (L.map (z9 0))=3) (Z:finrank KD (L.map (zD 0))=3) (x:finrank KD (zm L 0 0)=2) (P:yx) {T S:ze} (D:T∈zm L 0 0) (E:S∈zm L 0 0) {r0 a:Fin 3} (hb:qM (z7 0 0 T) r0 a) (Q:zn (z7 0 0 T)=0) (d:∀ i,i≠r0->∀ c,z7 0 0 S i c=0) (q:z7 0 0 S r0 a≠0) (hD:zp (z7 0 0 T) (z7 0 0 S)≠0):False:=by
 obtain⟨y,z,-⟩:=zN r0;obtain⟨t1,t2,-⟩:=zN a;have s:=jD g D E;have F:∀ Y∈L,zE (zp (wN Y) (qZ T)) (yT Y) (yW Y)=0:=λ Y f=>(qG g f D).2;have G:∀ Y∈L,zE (zp (wN Y) (qZ S)) (yT Y) (yW Y)=0:=λ Y f=>(qG g f E).2;have⟨A,B,R⟩:=xT g C p Z x;have U:zn (qZ T) r0 a=0:=by rw[Q];rfl
 rw[zK] at U;have⟨H,h,a0⟩:=hb;have k:qZ T (zV r0 1) (zV a 1)*qZ T (zV r0 0) (zV a 0)-qZ T (zV r0 0) (zV a 1)*qZ T (zV r0 1) (zV a 0)≠0:=by grind
 have⟨e,l,t,m,n⟩:=PG g C p x s h k d q;have I:∀ b,zp (wN e) (qZ T) r0 b=0:=λ b=>by have⟨Y,f,V⟩:=qz g p (Pi.single b 1);have:=(Z5 l F f).2;rw[Z4 _ _ _ r0 m n,t,one_mul,V] at this;simpa[Pi.single_apply] using this
 obtain⟨-,J,K,-,-,-,-,-,-⟩:=jB (wN e) (qZ T) (Or.inl ⟨rfl,rfl⟩) (Or.inl ⟨rfl,rfl⟩) H h;rw[I] at J K;have⟨k1,k2⟩:=jn (u:=wN e (zV r0 0) a) (v:=wN e (zV r0 1) a) k (by linear_combination -J) (by linear_combination -K);have M:yw L (zp (wN e) (qZ S)):=λ Y f=>by have:=(Z5 l G f).1;rw[Z4 _ _ _ r0 m n] at this;have W:=(j9 (wN Y) (qZ S) r0 (d _ (y.symm)) (d _ (z.symm))).1;simpa[W] using this
 have a1:zE (zp (qZ T) (qZ S)) A B≠0:=by grind
 set κ:=zE (zp (wN e) (qZ S)) A B/zE (zp (qZ T) (qZ S)) A B;have X:zp (wN e+(-κ)•qZ T) (qZ S)=0:=by rw[jv,xV,jv (qZ S),jv (qZ S)];refine R _ (kN M s _) ?_;rw[vA];simp only[κ];field_simp;ring
 have w:∀ i,i≠r0->(wN e+(-κ)•qZ T) i a=0:=λ i o=>by simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,h,mul_zero,add_zero];grind
 obtain⟨-,N,O⟩:=j9 (wN e+(-κ)•qZ T) (qZ S) r0 (d _ (y.symm)) (d _ (z.symm));simp only[X,Pi.zero_apply] at N O;refine PH g C p P D E l t (λ i o=>?_) d q κ (λ i o b=>?_)
 . rcases zO (r:=r0) i with rfl|rfl|rfl
   exacts[absurd rfl o,m,n]
 . rcases zO (r:=r0) i with rfl|rfl|rfl
   . exact absurd rfl o
   . exact Z6 _ _ r0 a _ q (w _ (y.symm)) (λ j=>(O j).symm) b
   . exact Z6 _ _ r0 a _ q (w _ (z.symm)) (λ j=>(N j).symm) b
lemma Z7 (d:zg L) (h:finrank KD L=6) (e:finrank KD (L.map (z9 0))=3) (m:finrank KD (L.map (zD 0))=3) (a:finrank KD (zm L 0 0)=2) (k:yx):jK ((zm L 0 0).map (z7 0 0)) (yw L):=by
 refine⟨?_,?_,λ M K c f n=>kN f n c,λ M f x=>yI d e m f x,xT d h e m a,?_,?_,?_⟩
 . have:=zW (qZ) (zm L 0 0);rw[j7,finrank_bot,a] at this;omega
 . rintro _ ⟨T,g,rfl⟩;have⟨o,p,q⟩:=qJ g;obtain⟨y,-,z,-⟩:=qb d o;have⟨A,B⟩:=wO p q;exact⟨λ Y C=>(qG d C g).1,A ▸ y,B ▸ z⟩
 . have⟨H,D,s⟩:∃ H∈zh L 0,yW H≠0:=by
    by_contra! t;exact xU h e a t
   exact⟨yW H,s,λ M f=>xS d e D f⟩
 . intro r l;refine jS d h e k (W:=zm L 0 0) inf_le_left (by rw[a]) (r0:=r) λ X u i E j=>cases ((qJ u).2.2 _) (λ b=>?_) j;have:=l _ ⟨X,u,rfl⟩ i E b;rwa[qL] at this
 . rintro _ ⟨T,g,rfl⟩ _ ⟨S,F,rfl⟩ r0 N G v w I _ J;exact PI d h e m a k g F G v w I J
lemma ja (L:Submodule KD ze):zm (L.map (zM:ze →ₗ[KD] ze)) 0 0=(zm L 0 0).map (zM:ze →ₗ[KD] ze):=by
 ext Y;constructor
 . intro e;obtain⟨⟨X,c,rfl⟩,a,b⟩:=qJ e;exact⟨X,yc c (λ j=>b j) (λ i=>a i),rfl⟩
 . rintro⟨X,c,rfl⟩;have⟨d,a,b⟩:=qJ c;exact yc ⟨X,d,rfl⟩ (λ j=>b j) (λ i=>a i)
lemma wa (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd2:finrank KD (zm L 0 0)=2) (hF3:yx):False:=by
 have c:∀ (f:ze →ₗ[KD] Fin 4->KD) (g:ze →ₗ[KD] Fin 4->KD),f.comp (zM:ze →ₗ[KD] ze)=g->(L.map (zM:ze →ₗ[KD] ze)).map f=L.map g:=λ f g h=>by rw[←map_comp,h]
 refine PE (Z7 hL h6 hr hc hd2 hF3) (Z7 (zX hL) ((zT L).trans h6) (by rw[c _ (zD 0) (LinearMap.ext λ X=>funext λ j=>rfl)];exact hc) (by rw[c _ (z9 0) (LinearMap.ext λ X=>funext λ j=>rfl)];exact hr) (by rw[ja,LinearEquiv.finrank_map_eq];exact hd2) hF3) λ A=>?_;rw[ja];constructor
 . rintro⟨_,⟨X,d,rfl⟩,rfl⟩;exact⟨X,d,rfl⟩
 . rintro⟨X,d,e⟩;exact⟨zM X,⟨X,d,rfl⟩,by funext a b;exact congrFun (congrFun e b) a⟩
lemma Z8 (hd3:finrank KD (zm L 0 0)=3) (f:ze →ₗ[KD] KD):2≤finrank KD (zm L 0 0⊓LinearMap.ker f:Submodule KD ze):=by have e:=zW f (zm L 0 0);have a:=finrank_le ((zm L 0 0).map f);rw[finrank_self] at a;omega
lemma PJ {L K:Submodule KD ze} (b:K≤zm L 0 0):finrank KD (K.map (z7 0 0))=finrank KD K:=by have e:=zW (qZ) K;rw[show K⊓LinearMap.ker (qZ)=⊥ from eq_bot_iff.2 λ X a=>by rw[←j7 (L:=L)];exact⟨b a.1,a.2⟩,finrank_bot,add_zero] at e;exact e
lemma kQ (j:zg L) {H:ze} (k:H∈zm L 0 0):∑ a,∑ b,z7 0 0 H a b=0/\zo (z7 0 0 H)=0:=by have⟨c,d,e⟩:=qJ k;obtain⟨f,-,g,-⟩:=qb j c;have⟨h,i⟩:=wO d e;exact⟨h ▸ f,i ▸ g⟩
lemma Z9 (M:zx) (x y:Fin 3->KD) {r0 a d e b c:Fin 3} (f:z6 r0 0=d) (g:z6 r0 1=e) (h:z6 a 0=b) (i:z6 a 1=c):zE M x y=y r0*(M r0 a*x a+M r0 b*x b+M r0 c*x c)+y d*(M d a*x a+M d b*x b+M d c*x c)+y e*(M e a*x a+M e b*x b+M e c*x c):=by subst f g h i;simp only[zE];rw[qU _ r0];simp only[qU _ a];ring
lemma PK (M:zx) (x y:Fin 3->KD) (r:Fin 3) (h:∀ b,M r b=0):zE M x y=y (z6 r 0)*∑ b,M (z6 r 0) b*x b+y (z6 r 1)*∑ b,M (z6 r 1) b*x b:=by simp only[zE];rw[qU _ r];simp only[h,mul_zero,zero_mul,sum_const_zero,zero_add,Finset.mul_sum,mul_assoc]
open LinearMap in
lemma PL (j:zg L) (z:finrank KD (L.map (z9 0))=3) (B:finrank KD (L.map (zD 0))=3) {T H:ze} (hT:T∈zm L 0 0) (hH:H∈zm L 0 0) {r0 c:Fin 3} (hb:qM (z7 0 0 T) r0 c) (a4:zn (z7 0 0 T)=0) (hs:z7 0 0 H r0 c=0):zp (z7 0 0 H) (z7 0 0 T)=0:=by
 have y:=jD j hH hT;have a0:yw L (zn (z7 0 0 H)):=λ Y k=>(qG j k hH).1;have⟨a1,a2,Q⟩:=hb;have a3:zn (z7 0 0 T) r0 c=0:=by rw[a4];rfl
 rw[zK] at a3;have⟨S,V,J⟩:=zN r0;have⟨W,X,K⟩:=zN c;have nb:=Q _ (S.symm) _ (W.symm);have ne:=Q _ (V.symm) _ (X.symm);obtain⟨-,g2,g3,g4,g5,C,N,O,Z⟩:=jB (z7 0 0 H) (z7 0 0 T) (Or.inl ⟨rfl,rfl⟩) (Or.inl ⟨rfl,rfl⟩) a1 a2;have cr:∀ x,x=r0\/x=z6 r0 0\/x=z6 r0 1:=λ x=>zO x;have cc:∀ x,x=c\/x=z6 c 0\/x=z6 c 1:=λ x=>zO x;generalize zp (z7 0 0 H) (z7 0 0 T)=M at *;generalize z7 0 0 H=A at *;generalize z7 0 0 T=U at *;generalize D:z6 r0 0=g at *;generalize E:z6 r0 1=l at *;generalize F:z6 c 0=m at *;generalize G:z6 c 1=i at *;rw[hs,mul_zero] at C N O Z;have hD:U l i*U g m-U l m*U g i≠0:=by grind
 have a5:U l i*U g m-U g i*U l m≠0:=by rwa[mul_comm (U g i)]
 by_contra hM;have hv:A g c≠0\/A l c≠0:=by
  by_contra! h;refine hM (yI j z B y (jo c λ b hb a=>?_));rcases cc b with rfl|rfl|rfl
  . exact absurd rfl hb
  . rcases cr a with rfl|rfl|rfl
    . rw[g2,h.1,h.2];ring
    . exact C
    . exact O
  . rcases cr a with rfl|rfl|rfl<;>grind
 have a6:A r0 m≠0\/A r0 i≠0:=by
  by_contra! h;refine hM (yI j z B y (qV r0 λ a ha b=>?_));rcases cr a with rfl|rfl|rfl
  . exact absurd rfl ha
  . rcases cc b with rfl|rfl|rfl
    . rw[g4,h.1,h.2];ring
    . exact C
    . exact N
  . rcases cc b with rfl|rfl|rfl<;>grind
 have ha:∀ Y∈L,zw Y c=0 -> zB Y r0=0:=by
  have I:∀ Y∈L⊓ker (qj c),qq r0 Y*(M r0 m•qj m+M r0 i•qj i) Y=0:=by intro Y k;have⟨n,o⟩:=Submodule.mem_inf.1 k;rw[mem_ker,zJ] at o;have e:=y Y n;rw[Z9 _ _ _ D E F G,o,C,N,O,Z] at e;simp only[LinearMap.add_apply,LinearMap.smul_apply,zJ,zG,smul_eq_mul];linear_combination e
  rcases zz _ _ _ I with h|h
  . exact λ Y k o=>h Y ⟨k,o⟩
  . exfalso;have⟨p,d,q⟩:=qz j z (Pi.single m 1);have⟨r,f,s⟩:=qz j z (Pi.single i 1);have v:=h p ⟨d,by simp[zJ,q,W]⟩;have w:=h r ⟨f,by simp[zJ,s,X]⟩;simp[zJ,q,s,K,K.symm] at v w;grind
 have R:∀ Y∈L,zB Y r0=0 -> zw Y c=0:=by
  have I:∀ Y∈L⊓ker (qq r0),qj c Y*(M g c•qq g+M l c•qq l) Y=0:=by intro Y k;have⟨n,P⟩:=Submodule.mem_inf.1 k;rw[mem_ker,zG] at P;have e:=y Y n;rw[Z9 _ _ _ D E F G,P,C,N,O,Z] at e;simp only[LinearMap.add_apply,LinearMap.smul_apply,zJ,zG,smul_eq_mul];linear_combination e
  rcases zz _ _ _ I with h|h
  . exact λ Y k P=>h Y ⟨k,P⟩
  . exfalso;have⟨p,d,t⟩:=qX j B (Pi.single g 1);have⟨r,f,u⟩:=qX j B (Pi.single l 1);have v:=h p ⟨d,by simp[zG,t,S]⟩;have w:=h r ⟨f,by simp[zG,u,V]⟩;simp[zG,t,u,J,J.symm] at v w;grind
 have I:∀ Y∈L⊓ker (qj c),(A l c•qq g+A g c•qq l) Y*(A r0 i•qj m+A r0 m•qj i) Y=0:=by intro Y k;have⟨n,o⟩:=Submodule.mem_inf.1 k;rw[mem_ker,zJ] at o;have e:=a0 Y n;rw[vu A _ _ D E F G o (ha Y n o) hs] at e;simp only[LinearMap.add_apply,LinearMap.smul_apply,zJ,zG,smul_eq_mul];linear_combination e
 rcases zz _ _ _ I with h|h
 . have⟨p,d,t⟩:=qX j B (Pi.single g 1);have⟨r,f,u⟩:=qX j B (Pi.single l 1);have v:=h p ⟨d,mem_ker.2 (R p d (by simp[t,S]))⟩;have w:=h r ⟨f,mem_ker.2 (R r f (by simp[u,V]))⟩;simp[zG,t,u,J,J.symm] at v w;grind
 . have⟨p,d,q⟩:=qz j z (Pi.single m 1);have⟨r,f,s⟩:=qz j z (Pi.single i 1);have v:=h p ⟨d,by simp[zJ,q,W]⟩;have w:=h r ⟨f,by simp[zJ,s,X]⟩;simp[zJ,q,s,K,K.symm] at v w;grind
open LinearMap in
lemma PM (hL:zg L) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd3:finrank KD (zm L 0 0)=3) {T:ze} (hT:T∈zm L 0 0) {r0 c0:Fin 3} (hb:qM (z7 0 0 T) r0 c0) (hTc:zn (z7 0 0 T)=0):False:=xX (N:=(zm L 0 0⊓ker (proj (r0.succ,c0.succ):ze →ₗ[KD] KD)).map (qZ)) (by rw[PJ inf_le_left];exact Z8 hd3 _) hb hTc (by rintro _ ⟨H,a,rfl⟩;exact PL hL hr hc hT a.1 hb hTc (by rw[qL];exact mem_ker.1 a.2)) (by rintro _ ⟨H,a,rfl⟩ b;exact yI hL hr hc (λ Y c=>(qG hL c a.1).1) b) (by rintro _ ⟨H,a,rfl⟩;exact(kQ hL a.1).1)
lemma PN (v:zg L) (w:finrank KD (L.map (z9 0))=3) (x:finrank KD (L.map (zD 0))=3) {A:zx} (y:yw L (zn A)) (l:∑ a,∑ b,A a b=0) (z:zo A=0) (r k:Fin 3) (m:A (z6 r 0) k=0) (n:A (z6 r 1) k=0) (o:A (z6 r 0) (z6 k 0)=A (z6 r 0) (z6 k 1)) (p:A (z6 r 1) (z6 k 0)=A (z6 r 1) (z6 k 1)):A (z6 r 0) (z6 k 1)=0/\A (z6 r 1) (z6 k 1)=0:=by
 have⟨c,B,d,e,f,g,h⟩:=kO A r k m n o p;obtain⟨i,-,-⟩:=zN k;rw[z,eq_comm] at c;simp only[mul_eq_zero,two_ne_zero,false_or] at c;have q:zn A=0:=by
  refine yI v w x y ?_;rcases c with(j|j)|j
  . refine jo k λ b C a=>?_
    rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
  . refine qV (zV r 0) λ a s b=>?_
    rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
  . refine qV (zV r 1) λ a s b=>?_
    rcases zO (r:=r) a with rfl|rfl|rfl<;>grind
 have t:=e _ (i.symm);have u:=f _ (i.symm);simp only[q,Pi.zero_apply] at d g h t u;rw[qU _ r] at l;simp only[qU _ k,m,n,o,p] at l;grind
def Za (U:zx) (i:Fin 3) (x:Fin 3->KD):ze →ₗ[KD] KD where
 toFun H:=∑ b,zp (z7 0 0 H) U i b*x b
 map_add' X Y:=by simp only[map_add,zR,Pi.add_apply,sum_univ_three];ring
 map_smul' c X:=by
  simp only[map_smul,zR,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,sum_univ_three]
  ring
open LinearMap in
lemma Zb (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd3:finrank KD (zm L 0 0)=3) (hF3:yx) {T:ze} (hT:T∈zm L 0 0) (hT0:z7 0 0 T≠0) {r0:Fin 3} (hU:∀ r,r≠r0->∀ c,z7 0 0 T r c=0):False:=by
 have⟨s1,s2,s3⟩:=zN r0;have d:=hU _ (s1.symm);have e:=hU _ (s2.symm);have g:∑ c,qZ T r0 c=0:=by have:=(kQ hL hT).1;rw[qU _ r0] at this;simpa[d,e] using this
 have u:qZ T r0≠0:=λ h=>hT0 (funext λ a=>by
  rcases zO (r:=r0) a with rfl|rfl|rfl
  exacts[h,funext d,funext e])
 have⟨e1,x,o⟩:=qX hL hc (Pi.single (zV r0 0) 1);have⟨e2,p,l⟩:=qX hL hc (Pi.single (zV r0 1) 1);set N:=zm L 0 0⊓ker (Za (qZ T) (zV r0 0) (yT e2)) with D
 have E:∀ H∈N,zp (qZ H) (qZ T)=0:=by
  rintro H ⟨F,G⟩;have y:=mem_ker.1 G;have I:=jD hL F hT;obtain⟨z0,-,-⟩:=j9 (qZ H) (qZ T) r0 d e;simp only[Za,LinearMap.coe_mk,AddHom.coe_mk] at y;generalize zp (qZ H) (qZ T)=M at *;have⟨κ,z⟩:=yF L (qq (zV r0 0)) (qq (zV r0 1)) ((qf λ b=>M (zV r0 1) b).comp yT) ((qf λ b=>M (zV r0 0) b).comp yT) x p (by simp[zG,o]) (by simp[zG,o,s3.symm]) (by simp[zG,l,s3]) (by simp[zG,l]) λ Y m=>by have:=I Y m;rw[PK _ _ _ r0 z0] at this;simpa only[LinearMap.comp_apply,qf,LinearMap.coe_mk,AddHom.coe_mk,zG] using this
  have A:κ=0:=by have:=(z e2 p).1;simp only[LinearMap.comp_apply,qf,LinearMap.coe_mk,AddHom.coe_mk,zG,l,single_eq_same,mul_one] at this;grind
  funext a b;have⟨Y,m,J⟩:=qz hL hr (Pi.single b 1);have k:=z Y m;simp only[A,zero_mul,neg_zero,LinearMap.comp_apply,qf,LinearMap.coe_mk,AddHom.coe_mk,J,qQ,mul_one] at k;show M a b=0;rcases zO (r:=r0) a with rfl|rfl|rfl
  exacts[z0 b,k.1,k.2]
 have B:∀ H∈N,(∀ c,qZ H (zV r0 0) c=0)/\∀ c,qZ H (zV r0 1) c=0:=by
  intro H f;obtain⟨-,z1,z2⟩:=j9 (qZ H) (qZ T) r0 d e;simp only[E H f,Pi.zero_apply] at z1 z2;by_cases t:∃ k0,qZ T r0 k0=0/\qZ T r0 (zV k0 0)≠0
  . have⟨k0,q,s⟩:=t;have⟨a1,a2⟩:=jq _ _ k0 (λ j=>(z1 j).symm) g q s;have⟨b1,b2⟩:=jq _ _ k0 (λ j=>(z2 j).symm) g q s;have⟨u0,v0⟩:=PN hL hr hc (λ Y m=>(qG hL m f.1).1) (kQ hL f.1).1 (kQ hL f.1).2 r0 k0 b1 a1 b2 a2;refine⟨λ c=>?_,λ c=>?_⟩<;>rcases zO (r:=k0) c with rfl|rfl|rfl<;>grind
  . push Not at t
    have w:∀ v:Fin 3->KD,(∀ j,qZ T r0 (zV j 0)*v (zV j 1)+qZ T r0 (zV j 1)*v (zV j 0)=0)->∀ c,v c=0:=by intro v K c;by_contra C;have⟨k0,k1,k2⟩:=jR _ v K g u (λ h=>C (congrFun h c));exact k2 (t k0 k1)
    exact⟨w _ λ j=>(z2 j).symm,w _ λ j=>(z1 j).symm⟩
 exact jS hL h6 hr hF3 (W:=N) (λ X n=>n.1.1) (Z8 hd3 _) (r0:=r0) λ X n i O j=>cases ((qJ n.1).2.2 _) (λ b=>by
  rcases zO (r:=r0) i with rfl|rfl|rfl
  . exact absurd rfl O
  . have:=(B X n).1 b;rwa[qL] at this
  . have:=(B X n).2 b;rwa[qL] at this) j
lemma we (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd3:finrank KD (zm L 0 0)=3) (hF3:yx):False:=by
 have⟨T,e,l,i⟩:=j8 hL h6 hr hc hd3;have d:qZ T≠0:=λ h=>l ((mem_bot KD).1 (by rw[←j7 (L:=L)];exact⟨e,LinearMap.mem_ker.2 h⟩));rcases qd _ d i with⟨r0,m⟩|⟨n,p⟩|⟨r0,n,a,b,c,-,-⟩
 . exact Zb hL h6 hr hc hd3 hF3 e d m
 . have k:∀ (f g:ze →ₗ[KD] Fin 4->KD),f.comp (zM:ze →ₗ[KD] ze)=g->(L.map (zM:ze →ₗ[KD] ze)).map f=L.map g:=λ f g h=>by
    rw[←map_comp,h]
   have o:∀ a b,qZ (zM T) a b=qZ T b a:=λ a b=>by rw[qL,qL,zQ]
   refine Zb (zX hL) ((zT L).trans h6) (by rw[k _ (zD 0) (LinearMap.ext λ X=>funext λ j=>rfl)];exact hc) (by rw[k _ (z9 0) (LinearMap.ext λ X=>funext λ j=>rfl)];exact hr) (by rw[ja,LinearEquiv.finrank_map_eq];exact hd3) hF3 (T:=zM T) (by rw[ja];exact⟨T,e,rfl⟩) (λ h=>d (funext λ a=>funext λ b=>by
    rw[←o];exact congrFun (congrFun h b) a)) (r0:=n) λ r q c=>by
    grind
 . exact PM hL hr hc hd3 e ⟨a,b,c⟩ i
end
section
open Module Submodule LinearMap
alias yJ:=Function.ne_iff
alias wP:=eq_of_le_of_finrank_le
alias kh:=mem_span_range_iff_exists_fun
alias wQ:=exists_mem_ne_zero_of_ne_bot
abbrev qi:=Fin 4-> KD
variable {L:Submodule KD ze}
def qa (a b c d:qi):KD:=a 0*(b 1*(c 2*d 3+c 3*d 2)+b 2*(c 1*d 3+c 3*d 1)+b 3*(c 1*d 2+c 2*d 1))+a 1*(b 0*(c 2*d 3+c 3*d 2)+b 2*(c 0*d 3+c 3*d 0)+b 3*(c 0*d 2+c 2*d 0))+a 2*(b 0*(c 1*d 3+c 3*d 1)+b 1*(c 0*d 3+c 3*d 0)+b 3*(c 0*d 1+c 1*d 0))+a 3*(b 0*(c 1*d 2+c 2*d 1)+b 1*(c 0*d 2+c 2*d 0)+b 2*(c 0*d 1+c 1*d 0))
def qo (a b c d:qi):ze:=λ x=>![a,b,c,d] x.1 x.2
def zL (a:qi):=a 0+a 1+a 2+a 3
def zr (a b:qi):=a 0*b 0+a 1*b 1+a 2*b 2+a 3*b 3
def qp (a b c:qi):=a 0*b 0*c 0+a 1*b 1*c 1+a 2*b 2*c 2+a 3*b 3*c 3
def wv (a b:qi):=zL a*zL b-zr a b
def qW (p a b:qi):=zL p*zL a*zL b-zL p*zr a b-zL a*zr p b-zL b*zr p a+2*qp p a b
lemma qN:(∀ (a b:qi) i,(a+b) i=a i+b i)/\(∀ (a:qi) (c:KD) i,(c•a) i=c*a i)/\(∀ (a b:qi) i,(a-b) i=a i-b i)/\(∀ (a:qi) i,(-a) i= -a i)/\(∀ (a b:qi) i,(a*b) i=a i*b i)/\(∀ i,(0:qi) i=0)/\∀ i,(1:qi) i=1:=by simp
lemma yY:(∀ (a b:qi) (c:KD),zr a (c•b)=c*zr a b)/\(∀ (a b:qi) (c:KD),zr (c•a) b=c*zr a b)/\(∀ a b c:qi,zr a (b+c)=zr a b+zr a c)/\(∀ a b c:qi,zr (a+b) c=zr a c+zr b c)/\(∀ a b:qi,zr a (-b)= -zr a b)/\(∀ a b:qi,zr (-a) b= -zr a b)/\(∀ (a:qi) (c:KD),zL (c•a)=c*zL a)/\(∀ a b:qi,zL (a+b)=zL a+zL b)/\(∀ a:qi,zL (-a)= -zL a)/\(∀ (a b d:qi) (c:KD),qp a b (c•d)=c*qp a b d)/\(∀ (a b d:qi) (c:KD),qp a (c•b) d=c*qp a b d)/\(∀ a b d:qi,qp a b (-d)= -qp a b d)/\∀ a b d:qi,qp a (-b) d= -qp a b d:=by refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩<;>intros<;>simp only[zr,zL,qp,qN]<;>ring
@[simp] theorem gaz:zL 0=0/\(∀ a,zr 0 a=0)/\(∀ a,zr a 0=0)/\(∀ a b,qp 0 a b=0)/\(∀ a b,qp a 0 b=0)/\(∀ a b,qp a b 0=0)/\(∀ a b,qW 0 a b=0)/\(∀ a b,qW a 0 b=0)/\(∀ a b,qW a b 0=0)/\(∀ a,wv 0 a=0)/\(∀ a,wv a 0=0)/\(∀ a b c,qa 0 a b c=0)/\(∀ a b c,qa a 0 b c=0)/\(∀ a b c,qa a b 0 c=0)/\∀ a b c,qa a b c 0=0:=by simp[zL,zr,qp,qW,wv,qa]
lemma ky:(∀ p,qa p 1 1 1=6*zL p)/\((∀ p u,qa p u 1 1=2*wv p u)/\(∀ p u,qa p 1 u 1=2*wv p u)/\∀ p u,qa p 1 1 u=2*wv p u)/\(∀ p u v,qa p u v 1=qW p u v)/\(∀ p u v,qa p u 1 v=qW p u v)/\∀ p u v,qa p 1 u v=qW p u v:=by refine ⟨?_,⟨?_,?_,?_⟩,?_,?_,?_⟩<;>intros<;>simp only[qa,zL,wv,qW,zr,qp,qN]<;>ring
lemma qO (a b:qi):zr a b=zr b a:=by simp only[zr];ring
lemma kR:∀ i:Fin 4,i=0\/i=1\/i=2\/i=3:=by decide
lemma PO (a b c d:qi):ql (λ i j=>qo a b c d (i,j))=qa a b c d:=by simp[zY,zs,qo,qa]
lemma vZ:qo 1 1 1 1∈zP L:=by rw[show qo 1 1 1 1=qk by funext ⟨i,j⟩;fin_cases i<;>simp[qk,qo]];exact mem_sup_right (mem_span_singleton_self _)
def yu (i:Fin 4):qi →ₗ[KD] ze where
 toFun p x:=if x.1=i then p x.2 else 0
 map_add' _ _:=by funext x;split_ifs<;>simp[*]
 map_smul' _ _:=by funext x;split_ifs<;>simp[*]
lemma jw:(∀ p,yu 0 p=qo p 0 0 0)/\(∀ p,yu 1 p=qo 0 p 0 0)/\(∀ p,yu 2 p=qo 0 0 p 0)/\(∀ p,yu 3 p=qo 0 0 0 p)/\(∀ a b c d e f g h:qi,qo a b c d+qo e f g h=qo (a+e) (b+f) (c+g) (d+h))/\(∀ (t:KD) (a b c d:qi),t•qo a b c d=qo (t•a) (t•b) (t•c) (t•d))/\(∀ a:qi,a+0=a)/\∀ a:qi,0+a=a:=by refine ⟨?_,?_,?_,?_,?_,?_,by simp,by simp⟩<;>intros<;>funext ⟨i,j⟩<;>fin_cases i<;>simp[yu,qo]
lemma yC {a b c d e f g k:qi} (h1:qo a b c d∈L) (h2:qo e f g k∈L):qo (a+e) (b+f) (c+g) (d+k)∈L:=by rw[← jw.2.2.2.2.1];exact L.add_mem h1 h2
lemma qh {a b c d e f g k:qi} (h1:qo a b c d∈L) (h2:qo e f g k∈L) (x y:KD):qo (x•a+y•e) (x•b+y•f) (x•c+y•g) (x•d+y•k)∈L:=yC (jw.2.2.2.2.2.1 x a b c d▸L.smul_mem x h1) (jw.2.2.2.2.2.1 y e f g k▸L.smul_mem y h2)
lemma Ky (x0 x1 x2 x3 t0 t1 t2 t3:qi) (s:KD):qa (x0+s•t0) (x1+s•t1) (x2+s•t2) (x3+s•t3)=qa x0 x1 x2 x3+s*(qa t0 x1 x2 x3+qa x0 t1 x2 x3+qa x0 x1 t2 x3+qa x0 x1 x2 t3)+s^2*(qa t0 t1 x2 x3+qa t0 x1 t2 x3+qa t0 x1 x2 t3+qa x0 t1 t2 x3+qa x0 t1 x2 t3+qa x0 x1 t2 t3)+s^3*(qa x0 t1 t2 t3+qa t0 x1 t2 t3+qa t0 t1 x2 t3+qa t0 t1 t2 x3)+s^4*qa t0 t1 t2 t3:=by simp only[qa,qN];ring
def wF:(Fin 4-> KD) →ₗ[KD] (Fin 4-> KD) →ₗ[KD] KD:=LinearMap.mk₂ KD zr (by intros;simp only[zr,qN];ring) (by intros;simp only[zr,qN,smul_eq_mul];ring) (by intros;simp only[zr,qN];ring) (by intros;simp only[zr,qN,smul_eq_mul];ring)
def wf:(Fin 4-> KD) →ₗ[KD] KD where
 toFun:=zL
 map_add' _ _:=by simp only[zL,qN];ring
 map_smul' _ _:=by simp only[zL,qN,smul_eq_mul,RingHom.id_apply];ring
lemma PQ {f:(Fin 4-> KD) →ₗ[KD] KD} {x y:Fin 4-> KD} (hx:f x=0) (hy:f y=0):∀ w∈span KD {x,y},f w=0:=λ w hw=>by obtain ⟨a,b,rfl⟩:=mem_span_pair.1 hw;simp[hx,hy]
lemma xd (U W:Submodule KD (Fin 4-> KD)) (h:∀ x∈U,∀ y∈W,zr x y=0):finrank KD U+finrank KD W≤4:=by
 have e:=qr wF U W h
 rw[show ker wF=⊥ from (Submodule.eq_bot_iff _).2 λ x hx=>by funext i;have:=LinearMap.congr_fun (mem_ker.1 hx) (Pi.single i 1);fin_cases i<;>simpa[wF,zr] using this,inf_bot_eq,finrank_bot,finrank_fin_fun] at e;omega
lemma Zz (P W:Submodule KD (Fin 4-> KD)) (h1:(λ _=>(1:KD))∉P) (hs:∀ w∈W,zL w=0) (h:∀ p∈P,∀ w∈W,zr p w=0):finrank KD P+finrank KD W≤3:=by
 have e:=finrank_sup_add_finrank_inf_eq P (span KD {λ _=>(1:KD)})
 rw[disjoint_iff.1 ((disjoint_span_singleton' (by simp[funext_iff])).2 h1),finrank_bot,finrank_span_singleton (by simp[funext_iff])] at e
 have:=xd (P⊔span KD {λ _=>(1:KD)}) W λ x hx w hw=>by
  obtain ⟨y,hy,z,hz,rfl⟩:=mem_sup.1 hx;obtain ⟨c,rfl⟩:=mem_span_singleton.1 hz;have a:=h y hy w hw;have b:=hs w hw;simp only[zr,zL,qN] at a b ⊢;linear_combination a+c*b
 omega
def qH (L:Submodule KD ze) (i:Fin 4):Submodule KD (Fin 4-> KD):=L.map (z9 i)
def qB (L:Submodule KD ze) (i:Fin 4):Submodule KD (Fin 4-> KD):=L.comap (yu i)
def vf (L:Submodule KD ze) (l m:Fin 4):Submodule KD ze:=L⊓ker (z9 l)⊓ker (z9 m)
abbrev k5 (j k l m:Fin 4):Prop:=j≠k/\j≠l/\j≠m/\k≠l/\k≠m/\l≠m
lemma wg {i:Fin 4}:qB L i≤qH L i:=λ p hp=>⟨_,hp,by funext c;simp[zA,yu]⟩
lemma yK {p:qi}:(p∈qB L 0↔ qo p 0 0 0∈L)/\(p∈qB L 1↔ qo 0 p 0 0∈L)/\(p∈qB L 2↔ qo 0 0 p 0∈L)/\(p∈qB L 3↔ qo 0 0 0 p∈L):=by simp only[qB,mem_comap,jw,true_and]
lemma kY:∀ j k l m r:Fin 4,k5 j k l m-> r=j\/r=k\/r=l\/r=m:=by decide
lemma ZA {j k l m:Fin 4} (h:k5 j k l m) {X} (hX:X∈vf L l m):X=yu j (z9 j X)+yu k (z9 k X):=by
 have a:=congrFun (mem_ker.1 hX.1.2);have b:=congrFun (mem_ker.1 hX.2);obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
 funext ⟨r,c⟩;rcases kY j k l m r ⟨h1,h2,h3,h4,h5,h6⟩ with e|e|e|e<;>subst e
 . simp[yu,h1,zA]
 . simp[yu,h1.symm,zA]
 . simpa[yu,h2.symm,h4.symm,zA] using a c
 . simpa[yu,h3.symm,h5.symm,zA] using b c
lemma ZB {j k l m:Fin 4} (h:k5 j k l m):finrank KD L≤finrank KD ((vf L l m).map (z9 j))+finrank KD (qB L k)+finrank KD (qH L l)+finrank KD (qH L m):=by
 have e1:=zW (z9 l) L;have e2:=zW (z9 m) (L⊓ker (z9 l))
 have e3:finrank KD ((L⊓ker (z9 l)).map (z9 m))≤finrank KD (qH L m):=finrank_mono (map_mono inf_le_left)
 have e4:=zW (z9 j) (vf L l m);have e5:=zW (z9 k) (vf L l m⊓ker (z9 j))
 have s:∀ X∈vf L l m⊓ker (z9 j),X=yu k (z9 k X):=λ X hX=>by have e:=ZA h hX.1;rwa[mem_ker.1 hX.2,map_zero,zero_add] at e
 rw[show vf L l m⊓ker (z9 j)⊓ker (z9 k)=⊥ from (Submodule.eq_bot_iff _).2 λ X hX=>by rw[s X hX.1,mem_ker.1 hX.2,map_zero],finrank_bot,add_zero] at e5
 have e6:finrank KD ((vf L l m⊓ker (z9 j)).map (z9 k))≤finrank KD (qB L k):=finrank_mono (by rintro _ ⟨X,hX,rfl⟩;show yu k _∈L;rw[← s X hX];exact hX.1.1.1)
 unfold vf qH at *;omega
lemma js (j k l m:Fin 4) (hd:finrank KD (qH L j)+finrank KD (qB L k)+finrank KD (qH L l)+finrank KD (qH L m)≤finrank KD L) {a} (ha:a∈qH L j) (h:k5 j k l m:=by decide):∃ b,yu j a+yu k b∈L:=by
 have:=ZB (L:=L) h
 have e:(vf L l m).map (z9 j)≤qH L j:=map_mono λ _ hX=>hX.1.1
 obtain ⟨X,hX,rfl⟩:a∈(vf L l m).map (z9 j):=(wP e (by omega))▸ha
 exact ⟨_,ZA h hX▸hX.1.1⟩
lemma kZ (j k l m:Fin 4) (hd:finrank KD (qB L k)+finrank KD (qH L l)+finrank KD (qH L m) < finrank KD L) (h:k5 j k l m:=by decide):∃ x y,x≠0/\yu j x+yu k y∈L:=by
 have:=ZB (L:=L) h
 obtain ⟨x,⟨X,hX,rfl⟩,x0⟩:=wQ (p:=(vf L l m).map (z9 j)) λ e=>by rw[e,finrank_bot] at this;omega
 exact ⟨_,_,x0,ZA h hX▸hX.1.1⟩
lemma xe (j k l m:Fin 4) (h:k5 j k l m:=by decide):finrank KD L≤finrank KD (qH L j)+finrank KD (qB L k)+finrank KD (qH L l)+finrank KD (qH L m):=by
 have:=ZB (L:=L) h;have:finrank KD ((vf L l m).map (z9 j))≤finrank KD (qH L j):=finrank_mono (map_mono λ _ hX=>hX.1.1);omega
lemma wx (x y z w:qi) (hx:zL x=0) (hy:zL y=0) (hz:zL z=0) (hw:zL w=0) (h1:zr x y=0) (h2:zr x z=0) (h3:zr x w=0) (h4:zr y z=0) (h5:zr y w=0) (h6:zr z w=0) (hxx:zr x x≠0) (hyy:zr y y≠0) (z0:z≠0) (w0:w≠0):False:=by
 obtain ⟨a,ha⟩:=yJ.1 z0;obtain ⟨b,hb⟩:=yJ.1 w0;simp only[zL,zr] at *
 fin_cases a<;>fin_cases b<;>simp at ha hb<;>grind
lemma vG (x y:qi) (h1:zL x=0) (h2:zL y=0) (h3:zr x x=0) (h4:zr y y=0) (h5:zr x y=0):∀ i j,x i*y j=x j*y i:=by
 simp only[zL,zr] at *;intro i j;fin_cases i<;>fin_cases j<;>simp<;>grind
lemma Y4 (n w:qi) (h1:zL n=0) (h2:zr n n=0) (h3:qp n n n=0) (g1:zL w=0) (g2:zr w n=0) (g3:qp w n n=0) (g4:qa w n n n=0) (i j:Fin 4) (hn:n i≠0) (hw:w j≠0):False:=by
 simp only[zL,zr,qp,qa] at *;fin_cases i<;>fin_cases j<;>simp at hn hw<;>grind
lemma vH {n m:qi} {i:Fin 4} (hi:n i≠0) (h:∀ i j,n i*m j=n j*m i):m=(m i/n i)•n:=funext λ j=>by have:=h i j;simp only[qN];field_simp;linear_combination this
lemma xf (w n m k:qi) (hw:zL w=0) (hn:zL n=0) (hm:zL m=0) (hk:zL k=0) (h1:zr n n=0) (h2:zr m m=0) (h3:zr k k=0) (h4:zr n m=0) (h5:zr n k=0) (h6:zr w n=0) (t1:qp w n m=0) (t2:qp n m k=0) (hp:qa w n m k=0) (n0:n≠0) (m0:m≠0) (k0:k≠0) (w0:w≠0):False:=by
 obtain ⟨i,hi⟩:=yJ.1 n0;obtain ⟨j,hj⟩:=yJ.1 w0
 have em:=vH hi (vG n m hn hm h1 h2 h4);have ek:=vH hi (vG n k hn hk h1 h3 h5)
 set μ:=m i/n i;set ν:=k i/n i
 have hμ:μ≠0:=λ h=>m0 (by rw[em,h,zero_smul])
 have hν:ν≠0:=λ h=>k0 (by rw[ek,h,zero_smul])
 rw[em] at t1;rw[em,ek] at t2 hp
 refine Y4 n w hn h1 ?_ hw h6 ?_ ?_ i j hi hj
 . have:μ*ν*qp n n n=0:=by rw[← t2];simp only[qp,qN];ring
   simpa[hμ,hν] using this
 . have:μ*qp w n n=0:=by rw[← t1];simp only[qp,qN];ring
   simpa[hμ] using this
 . have:μ*ν*qa w n n n=0:=by rw[← hp];simp only[qa,qN];ring
   simpa[hμ,hν] using this
lemma ZC {a b c d:qi} (sa:zL a=0) (sb:zL b=0) (sc:zL c=0) (sd:zL d=0) (dab:zr a b=0) (dac:zr a c=0) (dad:zr a d=0) (dbc:zr b c=0) (dbd:zr b d=0) (dcd:zr c d=0) (tabc:qp a b c=0) (tabd:qp a b d=0) (tacd:qp a c d=0) (tbcd:qp b c d=0) (hp:qa a b c d=0) (a0:a≠0) (b0:b≠0) (c0:c≠0) (d0:d≠0):False:=by
 have dba:=(qO a b).symm.trans dab;have dca:=(qO a c).symm.trans dac;have dda:=(qO a d).symm.trans dad;have dcb:=(qO b c).symm.trans dbc;have ddb:=(qO b d).symm.trans dbd;have ddc:=(qO c d).symm.trans dcd
 by_cases hb:zr b b=0
 . by_cases hc:zr c c=0
   . by_cases hd:zr d d=0
     . exact xf a b c d sa sb sc sd hb hc hd dbc dbd dab tabc tbcd hp b0 c0 d0 a0
     . have ha:zr a a=0:=by_contra λ ha=>wx a d b c sa sd sb sc dad dab dac ddb ddc dbc ha hd b0 c0
       exact xf d a b c sd sa sb sc ha hb hc dab dac dda (by rw[← tabd];simp only[qp];ring) tabc (by rw[← hp];simp only[qa];ring) a0 b0 c0 d0
   . have ha:zr a a=0:=by_contra λ ha=>wx a c b d sa sc sb sd dac dab dad dcb dcd dbd ha hc b0 d0
     have hd:zr d d=0:=by_contra λ hd=>wx c d a b sc sd sa sb dcd dca dcb dda ddb dab hc hd a0 b0
     exact xf c a b d sc sa sb sd ha hb hd dab dad dca (by rw[← tabc];simp only[qp];ring) tabd (by rw[← hp];simp only[qa];ring) a0 b0 d0 c0
 . have ha:zr a a=0:=by_contra λ ha=>wx a b c d sa sb sc sd dab dac dad dbc dbd dcd ha hb c0 d0
   have hc:zr c c=0:=by_contra λ hc=>wx b c a d sb sc sa sd dbc dba dbd dca dcd dad hb hc a0 d0
   have hd:zr d d=0:=by_contra λ hd=>wx b d a c sb sd sa sc dbd dba dbc dda ddc dac hb hd a0 c0
   exact xf b a c d sb sa sc sd ha hc hd dac dad dba (by rw[← tabc];simp only[qp];ring) tacd (by rw[← hp];simp only[qa];ring) a0 c0 d0 b0
lemma Y5 (p a b c u v w:qi) (s:KD):qa p (a+s•u) (b+s•v) (c+s•w)=qa p a b c+s*(qa p u b c+qa p a v c+qa p a b w)+s^2*(qa p u v c+qa p u b w+qa p a v w)+s^3*qa p u v w:=by simp only[qa,qN];ring
lemma wR {U:Submodule KD (Fin 4-> KD)} (h:finrank KD U=1):∃ x∈U,x≠0:=wQ λ e=>by subst e;simp at h
lemma Y6 {x y:Fin 4-> KD} (hx:x≠0) (h:finrank KD (span KD {x,y})≤1):∃ μ:KD,y=μ•x:=by
 obtain ⟨μ,hμ⟩:=mem_span_singleton.1 ((wP (span_mono (by simp):span KD {x}≤span KD {x,y}) (by rw[finrank_span_singleton hx];exact h))▸subset_span (by simp):y∈span KD {x});exact ⟨μ,hμ.symm⟩
lemma ZD (n:qi) (hn:n≠0) (hs:zL n=0) (κ:KD) (h:∀ i,n i*n i=κ*n i):False:=by
 obtain ⟨i,hi⟩:=yJ.1 hn;have:=h 0;have:=h 1;have:=h 2;have:=h 3;simp only[zL] at hs;fin_cases i<;>simp at hi<;>grind
lemma wy {P:Submodule KD (Fin 4-> KD)} (h1:(λ _=>(1:KD))∉P) (h2:finrank KD P=2) {n m:Fin 4-> KD} (n0:n≠0) (sn:zL n=0) (sm:zL m=0) (hn:∀ p∈P,zr n p=0) (hm:∀ p∈P,zr m p=0):∃ μ:KD,m=μ•n:=by
 have:=Zz P (span KD {n,m}) h1 (PQ (f:=wf) sn sm) λ p hp=>PQ (f:=wF p) ((qO _ _).trans (hn p hp)) ((qO _ _).trans (hm p hp));exact Y6 n0 (by omega)
lemma PR {P:Submodule KD (Fin 4-> KD)} (h1:(λ _=>(1:KD))∉P) (h2:finrank KD P=2) {n:Fin 4-> KD} (n0:n≠0) (sn:zL n=0) (dn:zr n n=0) (hn:∀ p∈P,zr n p=0) (hnn:∀ p∈P,zr (n*n) p=0):False:=by
 obtain ⟨κ,hκ⟩:=wy h1 h2 n0 sn (by simpa[zL,zr] using dn) hn hnn;exact ZD n n0 sn κ λ i=>by simpa using congrFun hκ i
lemma ki {i p} (h:finrank KD (qB L i)=0) (hp:yu i p∈L):p=0:=(mem_bot KD).1 (Submodule.finrank_eq_zero.1 h▸hp)
lemma Wj {U:Submodule KD (Fin 4-> KD)} (h:2≤finrank KD U):∃ v∈U,v≠0/\zL v=0:=by
 have e:=zW wf U;have:finrank KD (U.map wf)≤1:=(Submodule.finrank_le _).trans (by simp)
 obtain ⟨v,hv,v0⟩:=wQ (p:=U⊓ker wf) λ h'=>by rw[h',finrank_bot] at e;omega
 exact ⟨v,hv.1,v0,hv.2⟩
lemma PS (x d:qi) (c e:KD) (sx:zL x=0) (h1:∀ m,x m*d m=c*d m) (h2:∀ m,x m*x m=e*d m):x=0:=by simp only[zL] at sx;funext m;fin_cases m<;>simp<;>grind
lemma Y7 (v d:qi) (γ δ κ:KD) (sv:zL v=0) (dv:zr v v=0) (tv:qp v v v=0) (h2:∀ m,v m*v m=γ*d m) (sd:zL d=0) (hC:∀ m,qa (Pi.single m 1) v v v=δ*d m+κ) (a:Fin 4) (v0:v a≠0):False:=by
 have c0:=hC 0;have c1:=hC 1;have c2:=hC 2;have c3:=hC 3;simp only[zL,zr,qp,qa,Pi.single_apply] at sv dv tv sd c0 c1 c2 c3;simp at c0 c1 c2 c3;fin_cases a<;>simp at v0<;>grind
def PT (P:Submodule KD (Fin 4-> KD)):Submodule KD (Fin 4-> KD):=ker wf⊓ker (LinearMap.pi λ p:P=>wF p)
lemma PV {P:Submodule KD (Fin 4-> KD)} (h1:(λ _=>(1:KD))∉P) (h2:2≤finrank KD P):∃ d:Fin 4-> KD,zL d=0/\∀ w,zL w=0-> (∀ p∈P,zr p w=0)-> ∃ c:KD,∀ m,w m=c*d m:=by
 have:=Zz P (PT P) h1 (λ w hw=>hw.1) λ p hp w hw=>congrFun (mem_ker.1 hw.2) ⟨p,hp⟩
 obtain ⟨v,hv⟩:=finrank_le_one_iff.1 (show finrank KD (PT P)≤1 by omega)
 exact ⟨v,v.2.1,λ w s h=>let ⟨c,hc⟩:=hv ⟨w,s,mem_ker.2 (funext λ p=>h p p.2)⟩;⟨c,λ m=>by simpa using congrFun (congrArg Subtype.val hc).symm m⟩⟩
lemma Y8 {P:Submodule KD (Fin 4-> KD)} (h1:(λ _=>(1:KD))∉P) (h2:2≤finrank KD P) {n:Fin 4-> KD} (sn:zL n=0) (hn:∀ p∈P,zr p n=0) (n0:n≠0):∀ w,zL w=0-> (∀ p∈P,zr p w=0)-> ∃ c:KD,∀ m,w m=c*n m:=by
 obtain ⟨d,-,hd⟩:=PV h1 h2;obtain ⟨c0,h0⟩:=hd n sn hn
 have c00:c0≠0:=by rintro rfl;exact n0 (funext λ m=>by simp[h0])
 intro w s h;obtain ⟨c,hc⟩:=hd w s h;exact ⟨c/c0,λ m=>by rw[hc,h0];field_simp⟩
lemma Y9 (v:qi) (sv:zL v=0) (dv:zr v v=0) (h4:v 0^4+v 1^4+v 2^4+v 3^4=0):∃ b,v b=0:=by by_contra h;push Not at h;simp only[zL,zr] at *;grind
lemma Yc (v a0 a1 n:qi) (κ f0 g0 f1 g1 f2 g2:KD) (sv:zL v=0) (dv:zr v v=0) (hn:∀ m,n m=κ*(v m*v m)) (κ0:κ≠0) (nn:zr n n=0) (sa0:zL a0= -1) (sa1:zL a1= -1) (b0:∀ m,n m*a0 m=f0+g0*n m) (b1:∀ m,n m*a1 m=f1+g1*n m) (dd:zr a0 a1=1) (e:∀ m,a0 m+a1 m+2*a0 m*a1 m=f2+g2*n m) (fin:zr v n+2*qp a0 v n=0) (v0:v≠0):False:=by
 obtain ⟨b,hb⟩:=Y9 v sv dv (by have:κ^2*(v 0^4+v 1^4+v 2^4+v 3^4)=0:=(by rw[← nn];simp only[zr,hn];ring);simpa[κ0] using this)
 obtain ⟨a,ha⟩:=yJ.1 v0;have:=hn 0;have:=hn 1;have:=hn 2;have:=hn 3;have:=b0 0;have:=b0 1;have:=b0 2;have:=b0 3;have:=b1 0;have:=b1 1;have:=b1 2;have:=b1 3;have:=e 0;have:=e 1;have:=e 2;have:=e 3;clear hn b0 b1 e
 simp only[zL,zr,qp] at *;fin_cases b<;>fin_cases a<;>simp at hb ha<;>grind
lemma PW (p v0 v1 v2:qi) (π:KD) (π0:π≠0) (sp:zL p=0) {c d:Fin 4} (hcd:c≠d) (pc:p c=0) (pd:p d=0) (s0:zL v0=0) (s1:zL v1=0) (s2:zL v2=0) (d01:zr v0 v1=0) (d02:zr v0 v2=0) (d12:zr v1 v2=0) (t01:qp p v0 v1=0) (t02:qp p v0 v2=0) (t12:qp p v1 v2=0) (f0:zr p v0=π) (f1:zr p v1=π) (f2:zr p v2=π) (hp:qa p v0 v1 v2=0):False:=by
 simp only[zL,zr,qp,qa] at *;fin_cases c<;>fin_cases d<;>simp at hcd pc pd<;>grind
def PX (p v0 v1 v2 w0 w1 w2:qi):Prop:=qW p v0 v1=0/\qW p v0 v2=0/\qW p v1 v2=0/\qW p w0 w1=0/\qW p w0 w2=0/\qW p w1 w2=0/\qW p v0 w1=0/\qW p v0 w2=0/\qW p v1 w0=0/\qW p v1 w2=0/\qW p v2 w0=0/\qW p v2 w1=0/\qa p v0 v1 v2=0/\qa p w0 w1 w2=0/\qa p w0 w1 v2=0/\qa p w0 v1 w2=0/\qa p v0 w1 w2=0/\qa p w0 v1 v2=0/\qa p v0 w1 v2=0/\qa p v0 v1 w2=0
def vI (p:qi):(Fin 4-> KD) →ₗ[KD] (Fin 4-> KD) →ₗ[KD] KD:=LinearMap.mk₂ KD (qW p) (by intros;simp only[qW,zL,zr,qp,qN];ring) (by intros;simp only[qW,zL,zr,qp,qN,smul_eq_mul];ring) (by intros;simp only[qW,zL,zr,qp,qN];ring) (by intros;simp only[qW,zL,zr,qp,qN,smul_eq_mul];ring)
lemma PY {B:(Fin 4-> KD) →ₗ[KD] (Fin 4-> KD) →ₗ[KD] KD} {K:Submodule KD (Fin 4-> KD)} (hk:∀ x,(∀ y,B x y=0)-> x∈K) {k l:ℕ} {f:Fin k-> Fin 4-> KD} {g:Fin l-> Fin 4-> KD} (hf:LinearIndependent KD f) (hg:LinearIndependent KD g) (hfg:∀ a b,B (f a) (g b)=0):k+l≤4+finrank KD K:=by
 have e:=qr B (span KD (Set.range f)) (span KD (Set.range g)) λ x hx y hy=>by
  obtain ⟨c,rfl⟩:=(kh KD).1 hx;obtain ⟨d,rfl⟩:=(kh KD).1 hy;simp[map_sum,hfg]
 rw[finrank_span_eq_card hf,finrank_span_eq_card hg,finrank_fin_fun,Fintype.card_fin,Fintype.card_fin] at e
 have:finrank KD ↥(span KD (Set.range f)⊓ker B)≤finrank KD K:=finrank_mono λ x hx=>hk x λ y=>by simpa using LinearMap.congr_fun (mem_ker.1 hx.2) y
 omega
lemma vJ {k:ℕ} (f:Fin k-> Fin 4-> KD) (φ:Fin k-> (Fin 4-> KD) →ₗ[KD] KD) (h:(Matrix.of λ i j=>φ i (f j)).det≠0):LinearIndependent KD f:=by
 refine Fintype.linearIndependent_iff.2 λ c hc=>congrFun (Matrix.eq_zero_of_mulVec_eq_zero h (v:=c) (funext λ i=>?_))
 have:=congrArg (φ i) hc;simp only[map_sum,map_smul,smul_eq_mul,map_zero] at this
 simp only[Matrix.mulVec,dotProduct,Matrix.of_apply,Pi.zero_apply];rw[← this];exact Finset.sum_congr rfl λ j _=>mul_comm _ _
lemma PZ (p a b c:Fin 4-> KD) (m:Fin 4):(Matrix.of λ i j=>(![wf,wF p,proj m] i) (![a,b,c] j)).det=zL a*(zr p b*c m-b m*zr p c)-zL b*(zr p a*c m-a m*zr p c)+zL c*(zr p a*b m-a m*zr p b):=by simp[Matrix.det_fin_three,wf,wF];ring
lemma Yd (p:qi) (sp:zL p=0) (hp:∀ m,p m≠0) (x:Fin 4-> KD) (hx:∀ y,vI p x y=0):x∈(⊥:Submodule KD (Fin 4-> KD)):=by
 have e0:=hx (Pi.single 0 1);have e1:=hx (Pi.single 1 1);have e2:=hx (Pi.single 2 1);have e3:=hx (Pi.single 3 1)
 simp[vI,qW,zL,zr,qp] at e0 e1 e2 e3 sp;rw[mem_bot];funext m;fin_cases m<;>simp<;>grind
lemma xg (p v0 w0 x c d:qi) (π:KD) (π0:π≠0) (sp:zL p=0) (hp:∀ m,p m≠0) (s0:zL v0=0) (u0:zL w0=1) (f0:zr p v0=π) (e0:zr p w0=0) (hcs:zL c=0) (hcd:zr p c=π) (hds:zL d=1) (hdd:zr p d=0) (h1:qW p v0 c=0) (h2:qW p v0 d=0) (h3:qW p w0 c=0) (h4:qW p w0 d=0) (h5:qW p x c=0) (h6:qW p x d=0):(zL x=0-> zr p x=π-> x=v0)/\(zL x=1-> zr p x=0-> x=w0):=by
 have li2:LinearIndependent KD ![c,d]:=vJ _ ![wf,wF p] (by simp[Matrix.det_fin_two,wf,wF,hcs,hcd,hds,hdd,π0])
 have hB:∀ i j,vI p (![v0,w0,x] i) (![c,d] j)=0:=λ i j=>by fin_cases i<;>fin_cases j;exacts[h1,h2,h3,h4,h5,h6]
 refine ⟨λ hs hd=>funext λ m=>by_contra λ hm=>?_,λ hs hd=>funext λ m=>by_contra λ hm=>?_⟩<;>have:=PY (Yd p sp hp) (vJ _ ![wf,wF p,proj m] (by rw[PZ,s0,f0,u0,e0,hs,hd];intro h;exact hm (mul_left_cancel₀ π0 (by linear_combination -h)))) li2 hB<;>simp at this
lemma Ye (p w:qi) (sp:zL p=0) (hp:∀ m,p m≠0) (sw:zL w=1) (pw:zr p w=0) (tpw:qW p w w=0) (a3:qa p w w w=0) (ww:zr w w=1) (www:qp w w w=1):False:=by have:=hp 0;have:=hp 1;have:=hp 2;have:=hp 3;simp only[qW,zL,zr,qp,qa] at *;grind
def wS (m:Fin 4):qi:=λ k=>if k=m then -1 else 1
lemma Yf (p:qi) (m:Fin 4) (sp:zL p=0) (pm:p m=0) (hp:∀ k,k≠m-> p k≠0) (x:Fin 4-> KD) (hx:∀ y,vI p x y=0):x∈span KD {wS m}:=by
 have e0:=hx (Pi.single 0 1);have e1:=hx (Pi.single 1 1);have e2:=hx (Pi.single 2 1);have e3:=hx (Pi.single 3 1)
 simp[vI,qW,zL,zr,qp] at e0 e1 e2 e3 sp
 refine mem_span_singleton.2 ⟨(x 0+x 1+x 2+x 3)/2,funext λ k=>?_⟩
 have h0:=hp 0;have h1:=hp 1;have h2:=hp 2;have h3:=hp 3
 fin_cases m<;>simp[wS] at pm h0 h1 h2 h3 ⊢<;>fin_cases k<;>simp<;>grind
lemma ZE (p:qi) (m:Fin 4) (sp:zL p=0) (pm:p m=0) (y:qi):qW p (wS m) y=0/\zL (wS m)=2/\zr p (wS m)=0/\qa p (wS m) (wS m) y=2*zr p y:=by
 simp only[qW,zL,zr,qp,qa,wS] at sp ⊢;fin_cases m<;>simp at pm ⊢<;>refine ⟨?_,?_,?_,?_⟩<;>grind
lemma J0 (p v w:qi) (m:Fin 4) (π:KD) (π0:π≠0) (sp:zL p=0) (pm:p m=0) (sv:zL v=0) (pv:zr p v=π) (sw:zL w=1) (pw:zr p w=0) (hw:w≠(1/2:KD)•wS m):LinearIndependent KD ![v,w,wS m]:=by
 obtain ⟨k,hk⟩:=yJ.1 hw;obtain ⟨-,R2,R3,-⟩:=ZE p m sp pm 0
 refine vJ _ ![wf,wF p,proj k] ?_;rw[PZ,sv,pv,sw,pw,R2,R3];intro h;apply hk;simp only[qN];apply mul_left_cancel₀ π0;linear_combination h/2
lemma ZF (p vi wi vj wj:qi) (m:Fin 4) (π:KD) (π0:π≠0) (sp:zL p=0) (pm:p m=0) (hp:∀ k,k≠m-> p k≠0) (si:zL vi=0) (fi:zr p vi=π) (ui:zL wi=1) (ei:zr p wi=0) (sj:zL vj=0) (fj:zr p vj=π) (uj:zL wj=1) (ej:zr p wj=0) (b1:qW p vi vj=0) (b2:qW p vi wj=0) (b3:qW p wi vj=0) (b4:qW p wi wj=0):wi=(1/2:KD)•wS m\/wj=(1/2:KD)•wS m:=by
 by_contra h;push Not at h
 have R:=λ y=>(ZE p m sp pm y).1
 have S:∀ x y,qW p x y=qW p y x:=λ x y=>by simp only[qW,zL,zr,qp];ring
 have:=PY (Yf p m sp pm hp) (J0 p vi wi m π π0 sp pm si fi ui ei h.1) (J0 p vj wj m π π0 sp pm sj fj uj ej h.2) λ a b=>by fin_cases a<;>fin_cases b;exacts[b1,b2,(S _ _).trans (R vi),b3,b4,(S _ _).trans (R wi),R vj,R wj,R _]
 rw[finrank_span_singleton (by intro e;have:=congrFun e 0;fin_cases m<;>simp[wS] at this)] at this;omega
lemma xh {U:Submodule KD (Fin 4-> KD)} (hU:finrank KD U=2) {i j k l:Fin 4} (h:k5 i j k l) (hi:∀ u∈U,u i=0) (hj:∀ u∈U,u j=0):Pi.single k 1∈U/\Pi.single l 1∈U:=by
 obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
 have e:ker (proj (R:=KD) (φ:=λ _:Fin 4=>KD) i)⊓ker (proj (R:=KD) (φ:=λ _:Fin 4=>KD) j)=span KD (Set.range ![Pi.single k (1:KD),Pi.single l 1]):=by
  ext x;simp only[mem_inf,mem_ker,LinearMap.proj_apply,kh,Fin.sum_univ_two]
  refine ⟨λ ⟨hi,hj⟩=>⟨![x k,x l],funext λ m=>?_⟩,by rintro ⟨c,rfl⟩;simp[h2.symm,h3.symm,h4.symm,h5.symm]⟩
  rcases kY i j k l m ⟨h1,h2,h3,h4,h5,h6⟩ with rfl|rfl|rfl|rfl<;>simp[hi,hj,h2,h3,h4,h5,h6,h6.symm]
 rw[wP (show U≤span KD (Set.range ![Pi.single k (1:KD),Pi.single l 1]) from e▸λ u hu=>⟨hi u hu,hj u hu⟩) (by rw[finrank_span_eq_card (vJ _ ![proj k,proj l] (by simp[Matrix.det_fin_two,h6,h6.symm])),hU];simp)]
 exact ⟨subset_span ⟨0,rfl⟩,subset_span ⟨1,rfl⟩⟩
lemma xk {U:Submodule KD (Fin 4-> KD)} (hU:finrank KD U=2) {i j k l:Fin 4} (h:k5 i j k l) (hi:∀ u∈U,u i=0) (hj:∀ u∈U,u j=0) (hk:∀ u∈U,u k=0):False:=by have:=hk _ (xh hU h hi hj).1;simp at this
lemma ZG {a b c d:Fin 4} (h:k5 a b c d) (v w:qi):qa (Pi.single a 1) (Pi.single b 1) v w=v c*w d+v d*w c/\qa (Pi.single a 1+Pi.single b 1) (Pi.single a 1+Pi.single b 1) v w=2*(v c*w d+v d*w c):=by
 obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h;fin_cases a<;>fin_cases b<;>simp at h1<;>fin_cases c<;>simp at h2 h4<;>fin_cases d<;>simp at h3 h5 h6<;>constructor<;>simp[qa]<;>ring
lemma wT (f:qi) {a b c d:Fin 4} (h:k5 a b c d):f 0+f 1+f 2+f 3=f a+f b+f c+f d:=by
 obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h;rcases kR a with rfl|rfl|rfl|rfl<;>rcases kR b with rfl|rfl|rfl|rfl<;>rcases kR c with rfl|rfl|rfl|rfl<;>rcases kR d with rfl|rfl|rfl|rfl<;>first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | exact absurd rfl h4 | exact absurd rfl h5 | exact absurd rfl h6 | ring
lemma xl:∀ a b:Fin 4,a≠b-> ∃ c d,k5 a b c d:=by decide
lemma J3 {v w:qi} {i j k l:Fin 4} (D:k5 i j k l) (sv:zL v=0) (sw:zL w=0) (v0:v≠0) (w0:w≠0) (h:∀ m,v m*w m=0) (q1:v j*w l+v l*w j=0) (q2:v j*w k+v k*w j=0):False:=by
 simp only[zL] at sv sw;rw[wT v D] at sv;rw[wT w D] at sw;obtain ⟨a,ha⟩:=yJ.1 v0;obtain ⟨b,hb⟩:=yJ.1 w0
 have:=h i;have:=h j;have:=h k;have:=h l;clear h
 rcases kY i j k l a D with rfl|rfl|rfl|rfl<;>rcases kY _ _ _ _ b D with rfl|rfl|rfl|rfl<;>simp only[Pi.zero_apply] at ha hb<;>grind
lemma J4 {U0 U1:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) (n1:finrank KD U1=2) {v w:qi} (sv:zL v=0) (sw:zL w=0) (v0:v≠0) (w0:w≠0) (hz:∀ i,(∀ u∈U0,u i=0)\/∀ y∈U1,y i=0) (h:∀ i j k l,k5 i j k l-> (∀ u∈U0,u i=0)-> (∀ u∈U0,u j=0)-> (∀ y∈U1,y k=0)-> (∀ y∈U1,y l=0)-> ∀ m,v m*w m=0) (Q:∀ u∈U0,∀ y∈U1,qa u y v w=0):False:=by
 have P0:∀ {i j},i≠j-> (∀ u∈U0,u i=0)-> (∀ u∈U0,u j=0)-> False:=λ {i j} hij a b=>by
  obtain ⟨k,l,h1,h2,h3,h4,h5,h6⟩:=xl i j hij
  have c:=(hz k).resolve_left λ e=>xk n0 ⟨h1,h2,h3,h4,h5,h6⟩ a b e
  have d:=(hz l).resolve_left λ e=>xk n0 ⟨h1,h3,h2,h5,h4,h6.symm⟩ a b e
  obtain ⟨ek,el⟩:=xh n0 ⟨h1,h2,h3,h4,h5,h6⟩ a b;obtain ⟨ei,-⟩:=xh n1 ⟨h6,h2.symm,h4.symm,h3.symm,h5.symm,h1⟩ c d
  exact J3 ⟨h1,h2,h3,h4,h5,h6⟩ sv sw v0 w0 (h i j k l ⟨h1,h2,h3,h4,h5,h6⟩ a b c d) (by rw[← (ZG ⟨h2.symm,h4.symm,h6,h1,h3,h5⟩ v w).1];exact Q _ ek _ ei) (by rw[← (ZG ⟨h3.symm,h5.symm,h6.symm,h1,h2,h4⟩ v w).1];exact Q _ el _ ei)
 have P1:∀ {k l},k≠l-> (∀ y∈U1,y k=0)-> (∀ y∈U1,y l=0)-> False:=λ {k l} hkl c d=>by
  obtain ⟨i,j,h1,h2,h3,h4,h5,h6⟩:=xl k l hkl
  exact P0 h6 ((hz i).resolve_right λ e=>xk n1 ⟨h1,h2,h3,h4,h5,h6⟩ c d e) ((hz j).resolve_right λ e=>xk n1 ⟨h1,h3,h2,h5,h4,h6.symm⟩ c d e)
 rcases hz 0 with a|a<;>rcases hz 1 with b|b<;>rcases hz 2 with c|c
 exacts[P0 (by decide) a b,P0 (by decide) a b,P0 (by decide) a c,P1 (by decide) b c,P0 (by decide) b c,P1 (by decide) a c,P1 (by decide) a b,P1 (by decide) a b]
lemma Yg {v w:qi} {c d:Fin 4} (h1:v c*w d+v d*w c=0) (h2:v c*w c=0) (h3:v d*w d=0):(v c=0/\v d=0)\/(w c=0/\w d=0):=by grind
lemma J5 {U0 U1:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) (n1:finrank KD U1=2) {v w:qi} (hz:∀ i,v i*w i≠0-> (∀ u∈U0,u i=0)\/∀ y∈U1,y i=0) (t0:∀ u∈U0,qp u v w=0) (t1:∀ y∈U1,qp y v w=0) {i j k l:Fin 4} (h:k5 i j k l) (ni:v i*w i≠0) (nj:v j*w j≠0) (nk:v k*w k≠0):False:=by
 have P:∀ {U:Submodule KD (Fin 4-> KD)},finrank KD U=2-> (∀ u∈U,qp u v w=0)-> ∀ {a b c d},k5 a b c d-> (∀ u∈U,u a=0)-> (∀ u∈U,u b=0)-> v c*w c≠0-> False:=λ {U} nU tU {a b c d} hD ha hb nc=>nc (by have:=tU _ (xh nU hD ha hb).1;fin_cases c<;>simpa[qp] using this)
 obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
 rcases hz i ni with zi|zi<;>rcases hz j nj with zj|zj<;>rcases hz k nk with zk|zk
 exacts[P n0 t0 ⟨h1,h2,h3,h4,h5,h6⟩ zi zj nk,P n0 t0 ⟨h1,h2,h3,h4,h5,h6⟩ zi zj nk,P n0 t0 ⟨h2,h1,h3,h4.symm,h6,h5⟩ zi zk nj,P n1 t1 ⟨h4,h1.symm,h5,h2.symm,h6,h3⟩ zj zk ni,P n0 t0 ⟨h4,h1.symm,h5,h2.symm,h6,h3⟩ zj zk ni,P n1 t1 ⟨h2,h1,h3,h4.symm,h6,h5⟩ zi zk nj,P n1 t1 ⟨h1,h2,h3,h4,h5,h6⟩ zi zj nk,P n1 t1 ⟨h1,h2,h3,h4,h5,h6⟩ zi zj nk]
lemma J6 {z:qi} {a b c d:Fin 4} (h:k5 a b c d) (sz:zL z=0) (zc:z c=0) (zd:z d=0):z=z a•(Pi.single a 1-Pi.single b 1)/\∀ x:qi,zr z x=z a*(x a-x b):=by
 have e1:=wT z h;have e2:=λ x:qi=>wT (z*x) h;obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h;simp only[zL] at sz
 have zb:z b= -z a:=by rw[zc,zd] at e1;linear_combination sz-e1
 refine ⟨funext λ m=>?_,λ x=>?_⟩
 . rcases kY a b c d m ⟨h1,h2,h3,h4,h5,h6⟩ with rfl|rfl|rfl|rfl<;>simp[h1,h1.symm,h2.symm,h3.symm,h4.symm,h5.symm,zb,zc,zd]
 . have:=e2 x;simp only[zr,qN] at this ⊢;rw[this,zb,zc,zd];ring
lemma J7 {a b:Fin 4} (hab:a≠b) {U:Submodule KD (Fin 4-> KD)} (hU:finrank KD U=2) (h1U:(λ _=>(1:KD))∉U) (h:∀ u∈U,u a=u b):∃ u∈U,∃ α:KD,u=Pi.single a 1+Pi.single b 1-α•λ _=>1:=by
 have K:∀ x:Fin 4-> KD,wF (Pi.single a 1-Pi.single b 1) x=x a-x b:=λ x=>by fin_cases a<;>fin_cases b<;>simp at hab<;>simp[wF,zr]
 have e:=LinearMap.finrank_range_add_finrank_ker (wF (Pi.single a 1-Pi.single b 1))
 rw[LinearMap.range_eq_top.2 λ z=>⟨z•Pi.single a 1,by rw[K];simp[hab.symm]⟩,finrank_top,finrank_fin_fun,finrank_self] at e
 have ef:=finrank_sup_add_finrank_inf_eq U (span KD {λ _=>(1:KD)})
 rw[disjoint_iff.1 ((disjoint_span_singleton' (by simp[funext_iff])).2 h1U),finrank_bot,finrank_span_singleton (by simp[funext_iff])] at ef
 have le:U⊔span KD {λ _=>(1:KD)}≤ker (wF (Pi.single a 1-Pi.single b 1)):=sup_le (λ u hu=>by rw[mem_ker,K,h u hu,sub_self]) ((span_singleton_le_iff_mem _ _).2 (by rw[mem_ker,K];simp))
 have m:Pi.single a 1+Pi.single b 1∈U⊔span KD {λ _=>(1:KD)}:=(wP le (by omega))▸(by rw[mem_ker,K];simp[hab,hab.symm])
 obtain ⟨u,hu,z,hz,e⟩:=mem_sup.1 m;obtain ⟨α,rfl⟩:=mem_span_singleton.1 hz;exact ⟨u,hu,α,by rw[← e];simp⟩
lemma Yh (v w:qi) (h:∀ i,v i*w i=0) (sv:zL v=0) (sw:zL w=0) (v0:v≠0) (w0:w≠0) (i:Fin 4):v i≠0\/w i≠0:=by
 by_contra hc;push Not at hc;obtain ⟨a,ha⟩:=yJ.1 v0;obtain ⟨b,hb⟩:=yJ.1 w0;simp only[zL] at sv sw
 have:=h 0;have:=h 1;have:=h 2;have:=h 3;fin_cases i<;>fin_cases a<;>fin_cases b<;>simp at ha hb hc<;>grind
lemma wV {U:Submodule KD (Fin 4-> KD)} (hU:finrank KD U=2) {x y:Fin 4-> KD} (hx:x∈U) (hy:y∈U) (x0:x≠0) (hxy:∀ κ:KD,y≠κ•x):∀ u∈U,∃ a b:KD,u=a•x+b•y:=by
 have le:span KD (Set.range ![x,y])≤U:=span_le.2 (by rintro _ ⟨k,rfl⟩;fin_cases k;exacts[hx,hy])
 intro u hu;rw[← wP le (by rw[hU,finrank_span_eq_card ((LinearIndependent.pair_iff' x0).2 λ a e=>hxy a e.symm)];simp)] at hu
 obtain ⟨c,rfl⟩:=(kh KD).1 hu;exact ⟨c 0,c 1,by simp[Fin.sum_univ_two]⟩
lemma Yi {v w x b:Fin 4-> KD} (v0:v≠0) (w0:w≠0) (sv:zL v=0) (sw:zL w=0) (dvw:zr v w=0) (x0:x≠0) (b0:b≠0) (xb:∀ i,x i*b i=0) (xv:zr x v=0) (xw:zr x w=0) (bv:zr b v=0) (bw:zr b w=0) (tx:qp x v w=0) (tb:qp b v w=0):∃ α β:KD,∀ i,α*x i+β*b i=1:=by
 have liZ:LinearIndependent KD ![x,b]:=(LinearIndependent.pair_iff' x0).2 λ a e=>b0 (by obtain ⟨i,hi⟩:=yJ.1 x0;have:=xb i;rw[← e] at this;simp at hi;simp[hi] at this;rw[← e,this,zero_smul])
 obtain ⟨y1,y2,hY,hy⟩:∃ y1 y2:Fin 4-> KD,LinearIndependent KD ![y1,y2]/\∀ z,zr z v=0-> zr z w=0-> qp z v w=0-> zr z y1=0/\zr z y2=0:=by
  by_cases hdep:∃ κ:KD,w=κ•v
  . obtain ⟨κ,rfl⟩:=hdep;have κ0:κ≠0:=by rintro rfl;simp at w0
    refine ⟨v,v*v,(LinearIndependent.pair_iff' v0).2 λ a e=>ZD v v0 sv a λ i=>by simpa using (congrFun e i).symm,λ z hzv _ hzt=>⟨hzv,?_⟩⟩
    simp only[yY] at hzt;simp[κ0] at hzt;simpa[zr,qp,mul_assoc] using hzt
  push Not at hdep;exact ⟨v,w,(LinearIndependent.pair_iff' v0).2 λ a e=>hdep a e.symm,λ z hzv hzw _=>⟨hzv,hzw⟩⟩
 have hZ:∀ z∈span KD (Set.range ![x,b,λ _=>(1:KD)]),zr z y1=0/\zr z y2=0:=λ z hz=>by
  obtain ⟨c,rfl⟩:=(kh KD).1 hz;have ex:=hy x xv xw tx;have eb:=hy b bv bw tb
  have e1:=hy (λ _=>1) (by simpa[zr,zL] using sv) (by simpa[zr,zL] using sw) (by simpa[qp,zr] using dvw)
  simp[Fin.sum_univ_three,yY,ex,eb,e1]
 have p:=xd (span KD (Set.range ![x,b,λ _=>(1:KD)])) (span KD (Set.range ![y1,y2])) λ z hz y hy'=>by
  obtain ⟨c,rfl⟩:=(kh KD).1 hy';have:=hZ z hz;simp[Fin.sum_univ_two,yY,this.1,this.2]
 rw[finrank_span_eq_card hY,Fintype.card_fin] at p
 have e:=wP (span_mono (by rintro _ ⟨k,rfl⟩;fin_cases k;exacts[⟨0,rfl⟩,⟨1,rfl⟩]):span KD (Set.range ![x,b])≤span KD (Set.range ![x,b,λ _=>(1:KD)])) (by rw[finrank_span_eq_card liZ];simp;omega)
 obtain ⟨c,hc⟩:=(kh KD).1 (e▸subset_span ⟨2,rfl⟩:(λ _=>(1:KD))∈span KD (Set.range ![x,b]))
 exact ⟨c 0,c 1,λ i=>by simpa[Fin.sum_univ_two] using congrFun hc i⟩
lemma J8 {x v w:qi} {α:KD} {k l i j:Fin 4} (h:k5 k l i j) (xi:x i=0) (xj:x j=0) (ak:α*x k=1) (al:α*x l=1) (xv:zr x v=0) (xw:zr x w=0) (tx:qp x v w=0):v k*w k=0/\v l*w l=0:=by
 have e1:=wT (x*v) h;have e2:=wT (x*w) h;have e3:=wT (x*(v*w)) h;simp only[zr,qp,qN] at xv xw tx e1 e2 e3;rw[xi,xj] at e1 e2 e3
 have s1:v k+v l=0:=by linear_combination α*xv-α*e1-v k*ak-v l*al
 have s2:w k+w l=0:=by linear_combination α*xw-α*e2-w k*ak-w l*al
 have s3:v k*w k+v l*w l=0:=by linear_combination α*tx-α*e3-v k*w k*ak-v l*w l*al
 have:v k*w k=0:=by linear_combination (s3-w l*s1+v k*s2)/2
 exact ⟨this,by linear_combination w l*s1-v k*s2+this⟩
lemma J9 (u a b c:qi) (sa:zL a=0) (sb:zL b=0) (sc:zL c=0) (dab:zr a b=0) (dac:zr a c=0) (dbc:zr b c=0) (t:zr (a*b) c=0):qa u a b c= -6*zr (a*b*c) u:=by
 linear_combination (norm:=(simp only[qa,zL,zr,qN];ring1)) (zL u*zL b*zL c-zr u b*zL c-zr u c*zL b+2*zr (u*b) c)*sa+(-zr u a*zL c+2*zr (u*a) c)*sb+2*zr (u*a) b*sc+(-zL u*zL c+zr u c)*dab+(-zL u*zL b+zr u b)*dac+(-zL u*zL a+zr u a)*dbc+2*zL u*t
lemma Yj {p:qi} (p0:p≠0) (sp:zL p=0) (dp:zr p p=0) (κ:KD) (h:∀ m,p m*p m*p m=κ*p m):False:=by
 obtain ⟨i,hi⟩:=yJ.1 p0;have:=h 0;have:=h 1;have:=h 2;have:=h 3;simp only[zL,zr] at sp dp;fin_cases i<;>simp at hi<;>grind
lemma Yk {p w:qi} (p0:p≠0) (sp:zL p=0) (dp:zr p p=0) (sw:zL w=0) (ww:zr w w≠0) (h:∀ m,p m*w m=0):False:=by
 obtain ⟨i,hi⟩:=yJ.1 p0;have:=h 0;have:=h 1;have:=h 2;have:=h 3;simp only[zL,zr] at sp dp sw ww;fin_cases i<;>simp at hi<;>grind
lemma Yl {p w:qi} (p0:p≠0) (sp:zL p=0) (dp:zr p p=0) {b:Fin 4} (pb:p b=0) (sw:zL w=0) (dpw:zr p w=0) (ww:zr w w≠0) (l:KD) (h:∀ m,p m*p m*w m=l*(p m*w m)):False:=by
 obtain ⟨i,hi⟩:=yJ.1 p0;have:=h 0;have:=h 1;have:=h 2;have:=h 3;simp only[zL,zr] at sp dp sw dpw ww;fin_cases b<;>fin_cases i<;>simp at pb hi<;>grind
lemma Ym {p w:qi} (hp:∀ m,p m≠0) (sp:zL p=0) (sw:zL w=0) (w0:w≠0) (l:KD) (hl:∀ m,p m*w m=l*w m) (a κ:KD) (h:∀ m,p m*p m-a*p m=κ*w m):False:=by
 obtain ⟨j,hj⟩:=yJ.1 w0;have:=hp 0;have:=hp 1;have:=hp 2;have:=hp 3;have:=hl 0;have:=hl 1;have:=hl 2;have:=hl 3;have:=h 0;have:=h 1;have:=h 2;have:=h 3;simp only[zL] at sp sw;fin_cases j<;>simp at hj<;>grind
lemma kA {a b c:qi} (a0:a≠0) (sa:zL a=0) (sb:zL b=0) (sc:zL c=0) (hab:∀ m,a m*b m=0) (hac:∀ m,a m*c m=0) (dbc:zr b c=0) (dbb:zr b b≠0) (c0:c≠0):False:=by
 obtain ⟨i,hi⟩:=yJ.1 a0;obtain ⟨j,hj⟩:=yJ.1 c0;have:=hab 0;have:=hab 1;have:=hab 2;have:=hab 3;have:=hac 0;have:=hac 1;have:=hac 2;have:=hac 3;simp only[zL,zr] at sa sb sc dbc dbb;fin_cases i<;>fin_cases j<;>simp at hi hj<;>grind
lemma Yn {a b c:qi} (a0:a≠0) (sa:zL a=0) (sb:zL b=0) (sc:zL c=0) (dbc:zr b c=0) (dbb:zr b b≠0) (c0:c≠0) {β β':KD} (hb:∀ m,b m*a m=β*a m) (hc:∀ m,c m*a m=β'*a m) (hR:∀ x y,x≠y-> (∀ m,m≠x-> m≠y-> a m=0)-> False):False:=by
 obtain ⟨j,hj⟩:=yJ.1 c0;have:=hb 0;have:=hb 1;have:=hb 2;have:=hb 3;have:=hc 0;have:=hc 1;have:=hc 2;have:=hc 3
 have a0':¬(a 0=0/\a 1=0/\a 2=0/\a 3=0):=λ ⟨e0,e1,e2,e3⟩=>a0 (funext λ m=>by fin_cases m<;>simpa)
 simp only[zL,zr] at sa sb sc dbc dbb
 by_cases h0:a 0=0<;>by_cases h1:a 1=0<;>by_cases h2:a 2=0<;>by_cases h3:a 3=0<;>first
  | (refine hR 0 1 (by decide) λ m hx hy=>?_;fin_cases m<;>simp at hx hy ⊢<;>assumption)
  | (refine hR 0 2 (by decide) λ m hx hy=>?_;fin_cases m<;>simp at hx hy ⊢<;>assumption)
  | (refine hR 0 3 (by decide) λ m hx hy=>?_;fin_cases m<;>simp at hx hy ⊢<;>assumption)
  | (refine hR 1 2 (by decide) λ m hx hy=>?_;fin_cases m<;>simp at hx hy ⊢<;>assumption)
  | (refine hR 1 3 (by decide) λ m hx hy=>?_;fin_cases m<;>simp at hx hy ⊢<;>assumption)
  | (refine hR 2 3 (by decide) λ m hx hy=>?_;fin_cases m<;>simp at hx hy ⊢<;>assumption)
  | (fin_cases j<;>simp at hj<;>grind)
lemma ZH {p1 p2 p3 x:qi} (s1:zL p1=0) (s2:zL p2=0) (s3:zL p3=0) (d12:zr p1 p2=0) (d13:zr p1 p3=0) (d23:zr p2 p3=0) (i1:zr p1 p1≠0) (i2:zr p2 p2≠0) (p30:p3≠0) (sx:zL x=0) (dx:zr x p3=0):∃ α β:KD,x=α•p1+β•p2:=by
 refine ⟨zr x p1/zr p1 p1,zr x p2/zr p2 p2,?_⟩;by_contra hne
 have hd:∀ v,zr v (x-((zr x p1/zr p1 p1)•p1+(zr x p2/zr p2 p2)•p2))=zr v x-zr x p1/zr p1 p1*zr v p1-zr x p2/zr p2 p2*zr v p2:=λ v=>by simp only[zr,qN];ring
 have c1:=qO x p1;have c2:=qO x p2;have c3:=qO x p3;have c4:=qO p1 p2
 refine wx p1 p2 p3 _ s1 s2 s3 ?_ d12 d13 ?_ d23 ?_ ?_ i1 i2 p30 (sub_ne_zero.2 hne)
 . simp only[zL,qN] at s1 s2 sx ⊢;linear_combination sx-zr x p1/zr p1 p1*s1-zr x p2/zr p2 p2*s2
 . rw[hd,d12,← c1,div_mul_cancel₀ _ i1];ring
 . rw[hd,← c4,d12,← c2,div_mul_cancel₀ _ i2];ring
 . rw[hd,← qO p1 p3,← qO p2 p3,d13,d23,← c3,dx];ring
lemma v4 {U0:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) {z z' x:Fin 4-> KD} (hz:z∈U0) (hz':z'∈U0) (z0:z≠0) (nF:¬∀ u∈U0,zr x u=0) (e:zr x z=0) (e':zr x z'=0):∃ c:KD,z'=c•z:=by
 by_contra hc;push Not at hc;apply nF;intro u hu;obtain ⟨a,b,rfl⟩:=wV n0 hz hz' z0 hc u hu;simp[yY,e,e']
lemma ZI {U0:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) {z1 z2 z3:Fin 4-> KD} (Zp:∀ x,zr x z1=0-> zr x z2=0-> zr x z3=0-> ∀ u∈U0,zr x u=0) (z10:z1≠0) (h2:∃ c:KD,z2=c•z1) (h3:∃ c:KD,z3=c•z1):False:=by
 obtain ⟨c2,rfl⟩:=h2;obtain ⟨c3,rfl⟩:=h3;obtain ⟨m,hm⟩:=yJ.1 z10
 have e:=LinearMap.finrank_range_add_finrank_ker (wF z1)
 rw[LinearMap.range_eq_top.2 λ c=>⟨(c/z1 m)•Pi.single m 1,by fin_cases m<;>simp[wF,zr] at hm ⊢<;>field_simp⟩,finrank_top,finrank_fin_fun,finrank_self] at e
 have:=xd U0 (ker (wF z1)) λ u hu x hx=>by
  have hx':zr x z1=0:=by rw[qO];exact mem_ker.1 hx
  rw[qO];exact Zp x hx' (by simp[yY,hx']) (by simp[yY,hx']) u hu
 omega
lemma ZJ {U0:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) (one:(λ _=>(1:KD))∉U0) {p1 p2 p3 z1 z2 z3:qi} (Zp:∀ x,zr x z1=0-> zr x z2=0-> zr x z3=0-> ∀ u∈U0,zr x u=0) (E:∀ u∈U0,zr (p1*p2*p3) u=0) (s1:zL p1=0) (s2:zL p2=0) (s3:zL p3=0) (p10:p1≠0) (p20:p2≠0) (d12:zr p1 p2=0) (d13:zr p1 p3=0) (i1:zr p1 p1=0) (i2:zr p2 p2=0) (i3:zr p3 p3≠0) (t:zr (p1*p2) p3=0) (e1:zr p1 z1=0) (e2:zr p2 z2=0) (a12:zr (p1*p2) z1=0) (a21:zr (p2*p1) z2=0) (a13:zr (p1*p3) z1=0) (a23:zr (p2*p3) z2=0) (a31:zr (p3*p1) z3=0):False:=by
 obtain ⟨i,hi⟩:=yJ.1 p10
 obtain ⟨c,rfl⟩:∃ c:KD,p2=c•p1:=⟨_,vH hi (vG p1 p2 s1 s2 i1 i2 d12)⟩
 have c0:c≠0:=by rintro rfl;simp at p20
 have kk:∀ {A B:KD},A=0-> A=c*B-> B=0:=λ h e=>by rw[e] at h;simpa[c0] using h
 have tpw:zr (p1*p1) p3=0:=kk t (by simp only[zr,qN];ring)
 have pwU:∀ u∈U0,zr (p1*p3) u=0:=Zp _ a13 (kk a23 (by simp only[zr,qN];ring)) (by rw[← a31];simp only[zr,qN];ring)
 have ppwU:∀ u∈U0,zr (p1*p1*p3) u=0:=λ u hu=>kk (E u hu) (by simp only[zr,qN];ring)
 have pz2:zr p1 z2=0:=kk e2 (by simp only[zr,qN];ring)
 have ppz1:zr (p1*p1) z1=0:=kk a12 (by simp only[zr,qN];ring)
 have ppz2:zr (p1*p1) z2=0:=kk a21 (by simp only[zr,qN];ring)
 have w0:p3≠0:=λ h=>i3 (by simp[h])
 obtain ⟨l,hl⟩:=wy one n0 (λ h=>Yk p10 s1 i1 s3 i3 λ m=>by simpa using congrFun h m) (m:=p1*p1*p3) (by simpa[zL,zr] using d13) (by simpa[zL,zr] using tpw) pwU ppwU
 have hl':∀ m,p1 m*p1 m*p3 m=l*(p1 m*p3 m):=λ m=>by simpa using congrFun hl m
 by_cases hb:∃ b,p1 b=0
 . obtain ⟨b,hb⟩:=hb;exact Yl p10 s1 i1 hb s3 d13 i3 l hl'
 push Not at hb
 have hl2:∀ m,p1 m*p3 m=l*p3 m:=λ m=>mul_left_cancel₀ (hb m) (by linear_combination hl' m)
 have l0:l≠0:=by rintro rfl;apply w0;funext m;have:=hl2 m;simp only[zero_mul,mul_eq_zero] at this;exact this.resolve_left (hb m)
 have wU:∀ u∈U0,zr p3 u=0:=λ u hu=>by have h:=pwU u hu;rw[show zr (p1*p3) u=l*zr p3 u by simp only[zr,qN,hl2];ring] at h;simpa[l0] using h
 by_cases hpU:∀ u∈U0,zr p1 u=0
 . obtain ⟨κ,e⟩:=wy one n0 p10 s1 s3 hpU wU;exact i3 (by rw[e];simp[yY,i1])
 have pz3:zr p1 z3≠0:=λ h=>hpU (Zp p1 e1 pz2 h)
 set a:=zr (p1*p1) z3/zr p1 z3 with ha
 have hx:∀ z,zr (p1*p1-a•p1) z=zr (p1*p1) z-a*zr p1 z:=λ z=>by simp only[zr,qN];ring
 obtain ⟨κ,e⟩:=wy one n0 w0 s3 (m:=p1*p1-a•p1) (by simp only[zL,zr,qN] at s1 i1 ⊢;linear_combination i1-a*s1) wU (Zp _ (by rw[hx,ppz1,e1];ring) (by rw[hx,ppz2,pz2];ring) (by rw[hx,ha,div_mul_cancel₀ _ pz3,sub_self]))
 exact Ym hb s1 s3 w0 l hl2 a κ λ m=>by simpa using congrFun e m
lemma ZK {x y z:Fin 4-> KD} {c c₂:KD} (x0:x≠0) (h1:x=c•y) (h2:x=c₂•z):∃ k:KD,y=k•z:=by
 have c0:c≠0:=by rintro rfl;exact x0 (by rw[h1,zero_smul])
 exact ⟨c₂/c,by rw[div_eq_inv_mul,← smul_smul,← h2,h1,smul_smul,inv_mul_cancel₀ c0,one_smul]⟩
lemma xm {U0:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) {p1 p2 p3 z1 z2:qi} (hz1:z1∈U0) (hz2:z2∈U0) (z10:z1≠0) (z20:z2≠0) (nF1:¬∀ u∈U0,zr p1 u=0) (nF2:¬∀ u∈U0,zr p2 u=0) (s1:zL p1=0) (s2:zL p2=0) (s3:zL p3=0) (d12:zr p1 p2=0) (d13:zr p1 p3=0) (d23:zr p2 p3=0) (i1:zr p1 p1≠0) (i2:zr p2 p2≠0) (p30:p3≠0) (t:zr (p1*p2) p3=0) (e1:zr p1 z1=0) (e2:zr p2 z2=0) (a:zr (p1*p2) z1=0) (b:zr (p2*p1) z2=0) (nc:¬∃ c:KD,z2=c•z1):∀ m,p1 m*p2 m=0:=by
 have N12:zr p1 z2≠0:=λ h=>nc (v4 n0 hz1 hz2 z10 nF1 e1 h)
 have N21:zr p2 z1≠0:=λ h=>by obtain ⟨c,hc⟩:=v4 n0 hz2 hz1 z20 nF2 e2 h;exact nc (ZK z10 hc (one_smul KD z1).symm)
 obtain ⟨α,β,hx⟩:=ZH s1 s2 s3 d12 d13 d23 i1 i2 p30 (x:=p1*p2) (by simpa[zL,zr] using d12) t
 rw[mul_comm] at b
 have ea:zr (p1*p2) z1=α*zr p1 z1+β*zr p2 z1:=by rw[hx];simp[yY]
 have eb:zr (p1*p2) z2=α*zr p1 z2+β*zr p2 z2:=by rw[hx];simp[yY]
 rw[a,e1] at ea;rw[b,e2] at eb
 have β0:β=0:=by simpa[N21] using ea.symm
 have α0:α=0:=by simpa[N12] using eb.symm
 intro m;simpa[α0,β0] using congrFun hx m
lemma ZL (a b c:qi):zr (a*b) c=zr (b*c) a/\zr (a*b) c=zr (a*c) b/\zr (a*b*c)=zr (b*c*a)/\zr (a*b*c)=zr (a*c*b):=by
 refine ⟨?_,?_,?_,?_⟩<;>try (simp only[zr,qN];ring)
 all_goals (congr 1;ring)
lemma vK {U0:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) {p1 p2 p3 z1 z2 z3:qi} (hz1:z1∈U0) (hz2:z2∈U0) (hz3:z3∈U0) (z10:z1≠0) (z20:z2≠0) (z30:z3≠0) (Zp:∀ x,zr x z1=0-> zr x z2=0-> zr x z3=0-> ∀ u∈U0,zr x u=0) (s1:zL p1=0) (s2:zL p2=0) (s3:zL p3=0) (p10:p1≠0) (p20:p2≠0) (p30:p3≠0) (d12:zr p1 p2=0) (d13:zr p1 p3=0) (d23:zr p2 p3=0) (i1:zr p1 p1≠0) (i2:zr p2 p2≠0) (i3:zr p3 p3≠0) (t:zr (p1*p2) p3=0) (e1:zr p1 z1=0) (e2:zr p2 z2=0) (e3:zr p3 z3=0) (a12:zr (p1*p2) z1=0) (a21:zr (p2*p1) z2=0) (a31:zr (p3*p1) z3=0) (a32:zr (p3*p2) z3=0) (nF1:¬∀ u∈U0,zr p1 u=0) (nF2:¬∀ u∈U0,zr p2 u=0) (hR3:∀ x y,x≠y-> (∀ m,m≠x-> m≠y-> p3 m=0)-> False):False:=by
 have dt:=ZL p1 p2 p3
 have t13:zr (p1*p3) p2=0:=by rw[← dt.2.1];exact t
 have t23:zr (p2*p3) p1=0:=by rw[← dt.1];exact t
 have d21:=(qO p2 p1).trans d12;have d31:=(qO p3 p1).trans d13;have d32:=(qO p3 p2).trans d23
 obtain ⟨α,β,h13⟩:=ZH s1 s3 s2 d13 d12 d32 i1 i3 p20 (by simpa[zL,zr] using d13) t13
 obtain ⟨α₂,β₂,h23⟩:=ZH s2 s3 s1 d23 d21 d31 i2 i3 p10 (by simpa[zL,zr] using d23) t23
 have z3a:zr (p1*p3) z3=α*zr p1 z3:=by rw[h13];simp[yY,e3]
 have z3b:zr (p2*p3) z3=α₂*zr p2 z3:=by rw[h23];simp[yY,e3]
 rw[mul_comm] at a31 a32;rw[a31] at z3a;rw[a32] at z3b
 have m13:∀ m,p1 m*p3 m=α*p1 m+β*p3 m:=λ m=>by simpa using congrFun h13 m
 have m23:∀ m,p2 m*p3 m=α₂*p2 m+β₂*p3 m:=λ m=>by simpa using congrFun h23 m
 by_cases c12:∃ c:KD,z2=c•z1
 . have n13:zr p1 z3≠0:=λ h=>ZI n0 Zp z10 c12 (v4 n0 hz1 hz3 z10 nF1 e1 h)
   have n23:zr p2 z3≠0:=λ h=>by obtain ⟨c,hc⟩:=v4 n0 hz2 hz3 z20 nF2 e2 h;obtain ⟨c₂,hc₂⟩:=c12;exact ZI n0 Zp z10 ⟨c₂,hc₂⟩ ⟨c*c₂,by rw[hc,hc₂,smul_smul]⟩
   have α0:α=0:=by simpa[n13] using z3a.symm
   have α0₂:α₂=0:=by simpa[n23] using z3b.symm
   exact Yn (a:=p3) (b:=p1) (c:=p2) p30 s3 s1 s2 d12 i1 p20 (β:=β) (β':=β₂) (λ m=>by rw[m13,α0];ring) (λ m=>by rw[m23,α0₂];ring) hR3
 have P12:=xm n0 hz1 hz2 z10 z20 nF1 nF2 s1 s2 s3 d12 d13 d23 i1 i2 p30 t e1 e2 a12 a21 c12
 have α0:α≠0:=λ h=>by
  by_cases hβ:β=0
  . exact kA p10 s1 s2 s3 P12 (λ m=>by rw[m13,h,hβ];ring) d23 i2 p30
  . exact kA p20 s2 s1 s3 (λ m=>by rw[mul_comm];exact P12 m) (λ m=>(mul_eq_zero.1 (by have e:=m13 m;rw[h,zero_mul,zero_add] at e;linear_combination -p2 m*e+p3 m*P12 m:β*(p2 m*p3 m)=0)).resolve_left hβ) d13 i1 p30
 have α0₂:α₂≠0:=λ h=>by
  by_cases hβ:β₂=0
  . exact kA p20 s2 s1 s3 (λ m=>by rw[mul_comm];exact P12 m) (λ m=>by rw[m23,h,hβ];ring) d13 i1 p30
  . exact kA p10 s1 s2 s3 P12 (λ m=>(mul_eq_zero.1 (by have e:=m23 m;rw[h,zero_mul,zero_add] at e;linear_combination -p1 m*e+p3 m*P12 m:β₂*(p1 m*p3 m)=0)).resolve_left hβ) d23 i2 p30
 obtain ⟨c,hc⟩:=v4 n0 hz1 hz3 z10 nF1 e1 ((mul_eq_zero.1 z3a.symm).resolve_left α0)
 obtain ⟨c₂,hc₂⟩:=v4 n0 hz2 hz3 z20 nF2 e2 ((mul_eq_zero.1 z3b.symm).resolve_left α0₂)
 exact c12 (ZK z30 hc₂ hc)
lemma ZM {U0:Submodule KD (Fin 4-> KD)} (n0:finrank KD U0=2) (one:(λ _=>(1:KD))∉U0) {p1 p2 p3 z1 z2 z3:qi} (hz1:z1∈U0) (hz2:z2∈U0) (hz3:z3∈U0) (z10:z1≠0) (z20:z2≠0) (z30:z3≠0) (Zp:∀ x,zr x z1=0-> zr x z2=0-> zr x z3=0-> ∀ u∈U0,zr x u=0) (E:∀ u∈U0,zr (p1*p2*p3) u=0) (s1:zL p1=0) (s2:zL p2=0) (s3:zL p3=0) (p10:p1≠0) (p20:p2≠0) (p30:p3≠0) (d12:zr p1 p2=0) (d13:zr p1 p3=0) (d23:zr p2 p3=0) (t:zr (p1*p2) p3=0) (e1:zr p1 z1=0) (e2:zr p2 z2=0) (e3:zr p3 z3=0) (a12:zr (p1*p2) z1=0) (a21:zr (p2*p1) z2=0) (a13:zr (p1*p3) z1=0) (a31:zr (p3*p1) z3=0) (a23:zr (p2*p3) z2=0) (a32:zr (p3*p2) z3=0) (hR1:(∀ u∈U0,zr p1 u=0)-> ∀ x y,x≠y-> (∀ m,m≠x-> m≠y-> p1 m=0)-> False) (hR2:(∀ u∈U0,zr p2 u=0)-> ∀ x y,x≠y-> (∀ m,m≠x-> m≠y-> p2 m=0)-> False) (hR3:(∀ u∈U0,zr p3 u=0)-> ∀ x y,x≠y-> (∀ m,m≠x-> m≠y-> p3 m=0)-> False):False:=by
 have dt:=ZL p1 p2 p3
 have t23:zr (p2*p3) p1=0:=by rw[← dt.1];exact t
 have t13:zr (p1*p3) p2=0:=by rw[← dt.2.1];exact t
 have d21:=(qO p2 p1).trans d12;have d31:=(qO p3 p1).trans d13;have d32:=(qO p3 p2).trans d23
 by_cases i1:zr p1 p1=0<;>by_cases i2:zr p2 p2=0<;>by_cases i3:zr p3 p3=0
 . obtain ⟨i,hi⟩:=yJ.1 p10
   obtain ⟨c2,rfl⟩:∃ c:KD,p2=c•p1:=⟨_,vH hi (vG p1 p2 s1 s2 i1 i2 d12)⟩
   obtain ⟨c3,rfl⟩:∃ c:KD,p3=c•p1:=⟨_,vH hi (vG p1 p3 s1 s3 i1 i3 d13)⟩
   have c20:c2≠0:=by rintro rfl;simp at p20
   have c30:c3≠0:=by rintro rfl;simp at p30
   have tp:zr (p1*p1) p1=0:=by have:c2*c3*zr (p1*p1) p1=0:=(by rw[← t];simp only[zr,qN];ring);simpa[c20,c30] using this
   obtain ⟨μ,hμ⟩:=wy one n0 p10 s1 (m:=p1*p1*p1) (by simpa[zL,zr] using tp) (Zp p1 e1 (by simpa[yY,c20] using e2) (by simpa[yY,c30] using e3)) λ u hu=>by have:=E u hu;rw[show zr (p1*(c2•p1)*(c3•p1)) u=c2*c3*zr (p1*p1*p1) u by simp only[zr,qN];ring] at this;simpa[c20,c30] using this
   exact Yj p10 s1 i1 μ λ m=>by simpa using congrFun hμ m
 . exact ZJ n0 one Zp E s1 s2 s3 p10 p20 d12 d13 i1 i2 i3 t e1 e2 a12 a21 a13 a23 a31
 . exact ZJ n0 one (λ x h1 h3 h2=>Zp x h1 h2 h3) (λ u hu=>by rw[← dt.2.2.2];exact E u hu) s1 s3 s2 p10 p30 d13 d12 i1 i3 i2 t13 e1 e3 a13 a31 a12 a32 a21
 . exact wx p2 p3 p1 p1 s2 s3 s1 s1 d23 d21 d21 d31 d31 i1 i2 i3 p10 p10
 . exact ZJ n0 one (λ x h2 h3 h1=>Zp x h1 h2 h3) (λ u hu=>by rw[← dt.2.2.1];exact E u hu) s2 s3 s1 p20 p30 d23 d21 i2 i3 i1 t23 e2 e3 a23 a32 a21 a31 a12
 . exact wx p1 p3 p2 p2 s1 s3 s2 s2 d13 d12 d12 d32 d32 i2 i1 i3 p20 p20
 . exact wx p1 p2 p3 p3 s1 s2 s3 s3 d12 d13 d13 d23 d23 i3 i1 i2 p30 p30
 . have li:∀ {a b:qi},zr a b=0-> zr b b≠0-> ∀ (κ:KD),b=κ•a-> False:=λ hab hbb κ e=>hbb (by rw[e] at hab ⊢;simp[yY] at hab ⊢;simp[hab])
   have t31:zr (p3*p1) p2=0:=by rw[mul_comm,← dt.2.1];exact t
   by_cases F1:∀ u∈U0,zr p1 u=0
   . by_cases F2:∀ u∈U0,zr p2 u=0
     . obtain ⟨κ,e⟩:=wy one n0 p10 s1 s2 F1 F2;exact li d12 i2 κ e
     by_cases F3:∀ u∈U0,zr p3 u=0
     . obtain ⟨κ,e⟩:=wy one n0 p10 s1 s3 F1 F3;exact li d13 i3 κ e
     exact vK n0 hz2 hz3 hz1 z20 z30 z10 (λ x h2 h3 h1=>Zp x h1 h2 h3) s2 s3 s1 p20 p30 p10 d23 d21 d31 i2 i3 i1 t23 e2 e3 e1 a23 a32 a12 a13 F2 F3 (hR1 F1)
   by_cases F2:∀ u∈U0,zr p2 u=0
   . by_cases F3:∀ u∈U0,zr p3 u=0
     . obtain ⟨κ,e⟩:=wy one n0 p20 s2 s3 F2 F3;exact li d23 i3 κ e
     exact vK n0 hz3 hz1 hz2 z30 z10 z20 (λ x h3 h1 h2=>Zp x h1 h2 h3) s3 s1 s2 p30 p10 p20 d31 d32 d12 i3 i1 i2 t31 e3 e1 e2 a31 a13 a23 a21 F3 F1 (hR2 F2)
   by_cases F3:∀ u∈U0,zr p3 u=0
   . exact vK n0 hz1 hz2 hz3 z10 z20 z30 Zp s1 s2 s3 p10 p20 p30 d12 d13 d23 i1 i2 i3 t e1 e2 e3 a12 a21 a31 a32 F1 F2 (hR3 F3)
   have P13:=λ nc=>xm n0 hz1 hz3 z10 z30 F1 F3 s1 s3 s2 d13 d12 d32 i1 i3 p20 t13 e1 e3 a13 a31 nc
   have P23:=λ nc=>xm n0 hz2 hz3 z20 z30 F2 F3 s2 s3 s1 d23 d21 d31 i2 i3 p10 t23 e2 e3 a23 a32 nc
   by_cases c12:∃ c:KD,z2=c•z1
   . have nc13:¬∃ c:KD,z3=c•z1:=λ h=>ZI n0 Zp z10 c12 h
     have nc23:¬∃ c:KD,z3=c•z2:=λ ⟨c,hc⟩=>by obtain ⟨c₂,hc₂⟩:=c12;exact nc13 ⟨c*c₂,by rw[hc,hc₂,smul_smul]⟩
     exact kA p30 s3 s1 s2 (λ m=>by rw[mul_comm];exact P13 nc13 m) (λ m=>by rw[mul_comm];exact P23 nc23 m) d12 i1 p20
   have P12:=xm n0 hz1 hz2 z10 z20 F1 F2 s1 s2 s3 d12 d13 d23 i1 i2 p30 t e1 e2 a12 a21 c12
   by_cases c13:∃ c:KD,z3=c•z1
   . exact kA p20 s2 s1 s3 (λ m=>by rw[mul_comm];exact P12 m) (P23 λ ⟨c,hc⟩=>by obtain ⟨c₂,hc₂⟩:=c13;exact c12 (ZK z30 hc hc₂)) d13 i1 p30
   exact kA p10 s1 s2 s3 P12 (P13 c13) d23 i2 p30
lemma kB {p q z:qi} (sp:zL p=0) (sq:zL q=0) (dpq:zr p q=0) (h:qW p z q=0):zr (p*q) z=0:=by
 simp only[qW,sp,sq,dpq] at h;simp only[qp,zr,zL,qN] at h ⊢;linear_combination h/2
lemma Ja (p0:finrank KD (qB L 0)=0) {v1 v2 v3 z1 z2 z3 q1 q2 q3:qi} (S1:∀ u∈qH L 1,∃ a b:KD,u=a•v1+b•q1) (S2:∀ u∈qH L 2,∃ a b:KD,u=a•v2+b•q2) (S3:∀ u∈qH L 3,∃ a b:KD,u=a•v3+b•q3) (M1:qo 0 v1 0 0∈L) (M2:qo 0 0 v2 0∈L) (M3:qo 0 0 0 v3∈L) (Q1:qo z1 q1 0 0∈L) (Q2:qo z2 0 q2 0∈L) (Q3:qo z3 0 0 q3∈L):∀ u∈qH L 0,∃ a b c:KD,u=a•z1+b•z2+c•z3:=by
 rintro _ ⟨T,hT,rfl⟩;obtain ⟨a1,b1,e1⟩:=S1 _ ⟨T,hT,rfl⟩;obtain ⟨a2,b2,e2⟩:=S2 _ ⟨T,hT,rfl⟩;obtain ⟨a3,b3,e3⟩:=S3 _ ⟨T,hT,rfl⟩
 refine ⟨b1,b2,b3,?_⟩
 have key:=L.sub_mem hT (L.add_mem (L.add_mem (L.add_mem (L.add_mem (L.add_mem (L.smul_mem a1 M1) (L.smul_mem b1 Q1)) (L.smul_mem a2 M2)) (L.smul_mem b2 Q2)) (L.smul_mem a3 M3)) (L.smul_mem b3 Q3))
 rw[show T-(a1•qo 0 v1 0 0+b1•qo z1 q1 0 0+a2•qo 0 0 v2 0+b2•qo z2 0 q2 0+a3•qo 0 0 0 v3+b3•qo z3 0 0 q3)=qo (z9 0 T-(b1•z1+b2•z2+b3•z3)) 0 0 0 by
  funext ⟨r,c⟩;have f1:=congrFun e1 c;have f2:=congrFun e2 c;have f3:=congrFun e3 c;simp only[zA,qN] at f1 f2 f3;fin_cases r<;>simp[qo,zA,f1,f2,f3]] at key
 exact sub_eq_zero.1 (ki p0 (yK.1.2 key))
lemma Jb (σ:Equiv.Perm (Fin 4)) (i:Fin 4):qH (L.map (zq σ 1:ze →ₗ[KD] ze)) i=qH L (σ i)/\qB (L.map (zq σ 1:ze →ₗ[KD] ze)) i=qB L (σ i):=by
 have e:∀ p,zq σ 1 (yu (σ i) p)=yu i p:=λ p=>by funext ⟨r,c⟩;simp only[zy,yu,LinearMap.coe_mk,AddHom.coe_mk,Equiv.Perm.coe_one,id_eq,σ.injective.eq_iff]
 refine ⟨by unfold qH;rw[← map_comp];congr 1,?_⟩
 ext p;simp only[qB,mem_comap];rw[← e];exact ⟨λ ⟨X,hX,e'⟩=>(zq σ 1).injective e'▸hX,λ h=>⟨_,h,rfl⟩⟩
section
variable (hL:zg L)
include hL
lemma Yo {x0 x1 x2 x3 t0 t1 t2 t3:qi} (hX:qo x0 x1 x2 x3∈zP L) (hT:qo t0 t1 t2 t3∈L):qa t0 x1 x2 x3+qa x0 t1 x2 x3+qa x0 x1 t2 x3+qa x0 x1 x2 t3=0/\qa t0 t1 x2 x3+qa t0 x1 t2 x3+qa t0 x1 x2 t3+qa x0 t1 t2 x3+qa x0 t1 x2 t3+qa x0 x1 t2 t3=0/\qa x0 t1 t2 t3+qa t0 x1 t2 t3+qa t0 t1 x2 t3+qa t0 t1 t2 x3=0/\qa t0 t1 t2 t3=0:=by
 have k:∀ s:KD,qa (x0+s•t0) (x1+s•t1) (x2+s•t2) (x3+s•t3)=qa x0 x1 x2 x3:=λ s=>by
  have h:=(zP L).add_mem hX ((zP L).smul_mem s (mem_sup_left hT));rw[jw.2.2.2.2.2.1,jw.2.2.2.2.1] at h
  rw[← PO,← PO,yG hL h,yG hL hX,← jw.2.2.2.2.1,← jw.2.2.2.2.2.1,map_add,map_smul,yf hL hT,smul_zero,add_zero]
 have a:=k 1;have b:=k (-1);have c:=k 2;have d:=k (-2);rw[Ky] at a b c d
 exact ⟨by linear_combination (8*(a-b)-c+d)/12,by linear_combination (16*(a+b)-c-d)/24,by linear_combination (c-d-2*(a-b))/12,by linear_combination (c+d-4*(a+b))/24⟩
lemma y8 {t0 t1 t2 t3:qi} (hT:qo t0 t1 t2 t3∈L):zL t0+zL t1+zL t2+zL t3=0/\wv t0 t1+wv t0 t2+wv t0 t3+wv t1 t2+wv t1 t3+wv t2 t3=0/\qW t0 t1 t2+qW t0 t1 t3+qW t0 t2 t3+qW t1 t2 t3=0/\qa t0 t1 t2 t3=0:=by
 obtain ⟨a,b,c,d⟩:=Yo hL vZ hT;simp only[qa,zL,wv,qW,zr,qp,qN] at a b c d ⊢;exact ⟨by linear_combination a/6,by linear_combination b/2,by linear_combination c,d⟩
lemma ZN {i p} (hp:yu i p∈L) {x:Fin 4-> qi} (hX:qo (x 0) (x 1) (x 2) (x 3)∈zP L):qa p (x (z8 i 0)) (x (z8 i 1)) (x (z8 i 2))=0:=by
 rcases kR i with rfl|rfl|rfl|rfl<;>simp only[jw] at hp<;>have:=(Yo hL hX hp).1<;>simp[z8] at this ⊢<;>simp only[qa] at this ⊢<;>linear_combination this
lemma v5 {i p} (hp:yu i p∈L) {x t:Fin 4-> qi} (hX:qo (x 0) (x 1) (x 2) (x 3)∈zP L) (hT:qo (t 0) (t 1) (t 2) (t 3)∈L):let a:=z8 i;qa p (t (a 0)) (x (a 1)) (x (a 2))+qa p (x (a 0)) (t (a 1)) (x (a 2))+qa p (x (a 0)) (x (a 1)) (t (a 2))=0/\qa p (t (a 0)) (t (a 1)) (x (a 2))+qa p (t (a 0)) (x (a 1)) (t (a 2))+qa p (x (a 0)) (t (a 1)) (t (a 2))=0/\qa p (t (a 0)) (t (a 1)) (t (a 2))=0:=by
 have k:∀ s:KD,qa p (x (z8 i 0)+s•t (z8 i 0)) (x (z8 i 1)+s•t (z8 i 1)) (x (z8 i 2)+s•t (z8 i 2))=0:=λ s=>ZN hL hp (x:=λ r=>x r+s•t r) (by have:=(zP L).add_mem hX ((zP L).smul_mem s (mem_sup_left hT));rwa[jw.2.2.2.2.2.1,jw.2.2.2.2.1] at this)
 have a:=k 1;have b:=k (-1);have c:=k 2;have z:=ZN hL hp hX;rw[Y5] at a b c
 exact ⟨by linear_combination (6*a-2*b-c-3*z)/6,by linear_combination (a+b-2*z)/2,by linear_combination (c-3*a-b+3*z)/6⟩
lemma yz {i p} (hp:yu i p∈L):zL p=0:=by have:=ZN hL hp (x:=λ _=>1) vZ;simp only[ky.1] at this;linear_combination this/6
lemma qR {i p t0 t1 t2 t3} (hp:yu i p∈L) (hT:qo t0 t1 t2 t3∈L):let a:=z8 i;let r:=![t0,t1,t2,t3];zL p=0/\zr p (r (a 0))+zr p (r (a 1))+zr p (r (a 2))=0/\qW p (r (a 0)) (r (a 1))+qW p (r (a 0)) (r (a 2))+qW p (r (a 1)) (r (a 2))=0/\qa p (r (a 0)) (r (a 1)) (r (a 2))=0:=by
 obtain ⟨h1,h2,h3⟩:=v5 hL hp (x:=λ _=>1) (t:=![t0,t1,t2,t3]) vZ hT;have hs:=yz hL hp;simp only[ky.2.1,wv,hs] at h1;simp only[ky.2.2] at h2
 exact ⟨hs,by linear_combination -h1/2,h2,h3⟩
lemma vL (i):(λ _=>(1:KD))∉qB L i:=λ h=>qg hL i (wg h)
lemma Yp (h:∀ i,qB L i≠⊥):False:=by
 obtain ⟨a,ha,a0⟩:=wQ (h 0);obtain ⟨b,hb,b0⟩:=wQ (h 1);obtain ⟨c,hc,c0⟩:=wQ (h 2);obtain ⟨d,hd,d0⟩:=wQ (h 3)
 have Mb:=yK.2.1.1 hb;have Mc:=yK.2.2.1.1 hc;have Md:=yK.2.2.2.1 hd;have sa:=yz hL ha;have sb:=yz hL hb;have sc:=yz hL hc;have sd:=yz hL hd
 have dab:=(qR hL ha Mb).2.1;have dac:=(qR hL ha Mc).2.1;have dad:=(qR hL ha Md).2.1;have dbc:=(qR hL hb Mc).2.1;have dbd:=(qR hL hb Md).2.1;have dcd:=(qR hL hc Md).2.1
 have tabc:=(qR hL ha (yC Mb Mc)).2.2.1;have tabd:=(qR hL ha (yC Mb Md)).2.2.1;have tacd:=(qR hL ha (yC Mc Md)).2.2.1;have tbcd:=(qR hL hb (yC Mc Md)).2.2.1;have hp:=(qR hL ha (yC (yC Mb Mc) Md)).2.2.2
 simp[z8] at dab dac dad dbc dbd dcd;simp[z8,qW,sa,sb,sc,sd,dab,dac,dad,dbc,dbd,dcd] at tabc tabd tacd tbcd hp
 exact ZC sa sb sc sd dab dac dad dbc dbd dcd tabc tabd tacd tbcd hp a0 b0 c0 d0
lemma Jc (h2:finrank KD (qB L 2)=2) (h3:finrank KD (qB L 3)=2):False:=by
 have:=Zz _ (qB L 3) (vL hL 2) (λ _ h=>yz hL h) λ p hp q hq=>by simpa[z8] using (qR hL hp (yK.2.2.2.1 hq)).2.1
 omega
lemma Jd (h3:finrank KD (qB L 3)=2) (h1:qB L 1≠⊥) (h2:qB L 2≠⊥):False:=by
 obtain ⟨n,hn,n0⟩:=wQ h1;obtain ⟨m,hm,m0⟩:=wQ h2
 have sn:=yz hL hn;have Mn:=yK.2.1.1 hn;have Mm:=yK.2.2.1.1 hm
 have dpn:∀ p∈qB L 3,zr n p=0:=λ p hp=>by rw[qO];simpa[z8] using (qR hL hp Mn).2.1
 obtain ⟨μ,rfl⟩:=wy (vL hL 3) h3 n0 sn (yz hL hm) dpn λ p hp=>by rw[qO];simpa[z8] using (qR hL hp Mm).2.1
 have μ0:μ≠0:=by rintro rfl;simp at m0
 refine PR (vL hL 3) h3 n0 sn (by simpa[z8,yY,μ0] using (qR hL hn Mm).2.1) dpn λ p hp=>?_
 have:=(qR hL hp (yC Mn Mm)).2.2.1;simp[z8,qW,yz hL hp,sn,(qO _ _).trans (dpn p hp),yY,μ0] at this;simpa[zr,qp,mul_comm,mul_left_comm] using this
lemma Yq {i j:Fin 4} (hij:i≠j) {p a u:qi} (hp:yu i p∈L) (hT:yu i a+yu j u∈L):zr p u=0:=by
 rcases kR i with rfl|rfl|rfl|rfl<;>rcases kR j with rfl|rfl|rfl|rfl<;>simp only[jw] at hT<;>first | exact absurd rfl hij | simpa[z8] using (qR hL hp hT).2.1
lemma Yr {v b1 b2 b3:qi} (h1:qo v b1 0 0∈L) (h2:qo v 0 b2 0∈L) (h3:qo v 0 0 b3∈L) (sv:zL v=0):zL b1=0/\zL b2=0/\zL b3=0/\zr v b1=0/\zr v b2=0/\zr v b3=0/\zr b1 b2=0/\zr b1 b3=0/\zr b2 b3=0/\qp v b1 b2=0/\qp v b1 b3=0/\qp v b2 b3=0/\qp b1 b2 b3=0/\qa v b1 b2 b3=0:=by
 have c1:=y8 hL h1;have c2:=y8 hL h2;have c3:=y8 hL h3;have e12:=y8 hL (qh h1 h2 1 (-1));have e13:=y8 hL (qh h1 h3 1 (-1));have e23:=y8 hL (qh h2 h3 1 (-1));have f12:=y8 hL (qh h1 h2 1 1);have f13:=y8 hL (qh h1 h3 1 1);have f23:=y8 hL (qh h2 h3 1 1);have f123:=y8 hL (qh (qh h1 h2 1 1) h3 1 (-2));have f0:=y8 hL (qh (qh h1 h2 1 1) h3 1 1)
 simp only[zL,wv,qW,zr,qp,qa,qN] at c1 c2 c3 e12 e13 e23 f12 f13 f23 f123 f0 sv ⊢
 obtain ⟨c1a,c1b,-,-⟩:=c1;obtain ⟨c2a,c2b,-,-⟩:=c2;obtain ⟨c3a,c3b,-,-⟩:=c3;obtain ⟨-,e12b,-,-⟩:=e12;obtain ⟨-,e13b,-,-⟩:=e13;obtain ⟨-,e23b,-,-⟩:=e23;obtain ⟨-,-,f12c,-⟩:=f12;obtain ⟨-,-,f13c,-⟩:=f13;obtain ⟨-,-,f23c,-⟩:=f23;obtain ⟨-,-,f123c,-⟩:=f123;obtain ⟨-,-,-,f0d⟩:=f0
 and_intros<;>grind
lemma Je {v b1 b2:qi} (h1:qo v b1 0 0∈L) (h2:qo v 0 b2 0∈L) (sv:zL v=0):zL b1=0/\zL b2=0/\zr v b1=0/\zr v b2=0/\zr b1 b2=0/\qp v b1 b2=0:=by
 have c1:=y8 hL h1;have c2:=y8 hL h2;have e:=y8 hL (qh h1 h2 1 (-1));have f:=y8 hL (qh h1 h2 1 1)
 simp only[zL,wv,qW,zr,qp,qa,qN] at c1 c2 e f sv ⊢;obtain ⟨c1a,c1b,-,-⟩:=c1;obtain ⟨c2a,c2b,-,-⟩:=c2;obtain ⟨-,e,-,-⟩:=e;obtain ⟨-,-,f,-⟩:=f;and_intros<;>grind
lemma wW {p:qi} (hp:p∈qB L 3) {t0 t1 t2:qi} (hT:qo t0 t1 t2 0∈L) (s0:zL t0=0) (s1:zL t1=0) (s2:zL t2=0):zr p t0+zr p t1+zr p t2=0/\qp p t0 t1+qp p t0 t2+qp p t1 t2=0/\qa p t0 t1 t2=0:=by
 obtain ⟨sp,h1,h2,h3⟩:=qR hL hp hT;simp[z8] at h1 h2 h3;refine ⟨h1,?_,h3⟩;simp only[qW,sp,s0,s1,s2] at h2;linear_combination h2/2
lemma Jf (p3:finrank KD (qB L 3)=2) {v b1 b2:qi} (h1:qo v b1 0 0∈L) (h2:qo v 0 b2 0∈L) (sv:zL v=0) (v0:v≠0) (z1:b1≠0):False:=by
 obtain ⟨s1,s2,d1,d2,d12,t12⟩:=Je hL h1 h2 sv;obtain ⟨d,sd,hd⟩:=PV (vL hL 3) p3.ge
 have A:=λ p (hp:p∈qB L 3)=>wW hL hp h1 sv s1 gaz.1
 have B:=λ p (hp:p∈qB L 3)=>wW hL hp h2 sv gaz.1 s2
 have C:=λ p (hp:p∈qB L 3)=>wW hL hp (by simpa using qh h1 h2 1 (-1):qo 0 b1 (-b2) 0∈L) gaz.1 s1 (by simp[yY,s2])
 have E:=λ p (hp:p∈qB L 3)=>wW hL hp (by simpa using qh h1 h2 1 1:qo (v+v) b1 b2 0∈L) (by simp[yY,sv]) s1 s2
 obtain ⟨α,hα⟩:=hd (v+b1) (by simp[yY,sv,s1]) λ p hp=>by simpa[yY] using (A p hp).1
 obtain ⟨β,hβ⟩:=hd (v+b2) (by simp[yY,sv,s2]) λ p hp=>by simpa[yY] using (B p hp).1
 obtain ⟨γ1,g1⟩:=hd (v*b1) (by simpa[zL,zr] using d1) λ p hp=>by simpa[zr,qp,mul_assoc] using (A p hp).2.1
 obtain ⟨γ2,g2⟩:=hd (v*b2) (by simpa[zL,zr] using d2) λ p hp=>by simpa[zr,qp,mul_assoc] using (B p hp).2.1
 obtain ⟨γ3,g3⟩:=hd (b1*b2) (by simpa[zL,zr] using d12) λ p hp=>by have:=(C p hp).2.1;simp[yY] at this;simpa[zr,qp,mul_assoc] using this
 set κ:=(∑ m,qa (Pi.single m 1) v b1 b2)/4
 obtain ⟨δ,hδ⟩:=hd (λ m=>qa (Pi.single m 1) v b1 b2-κ) (by simp only[zL,κ,Fin.sum_univ_four];ring) λ p hp=>by
  have e:=(E p hp).2.2;have sp:=yz hL hp;simp only[zr,zL,qa,Pi.single_apply,qN] at e sp ⊢;simp;linear_combination e/2-κ*sp
 simp only[qN] at hα hβ g1 g2 g3
 by_cases hab:α=β
 . subst hab;by_cases ha:α=0
   . subst ha;obtain ⟨a,ha⟩:=yJ.1 v0
     have e1:b1=-v:=funext λ m=>by simp only[qN];linear_combination hα m
     have e2:b2=-v:=funext λ m=>by simp only[qN];linear_combination hβ m
     subst e1 e2;exact Y7 v d (-γ1) δ κ sv (by simpa[yY] using d1) (by simpa[yY] using t12) (λ m=>by simp only[qN] at g1;linear_combination -g1 m) sd (λ m=>by have:=hδ m;simp only[qa,qN] at this ⊢;linear_combination this) a ha
   . exact z1 (PS b1 d ((γ1+γ3)/α) γ3 s1 (λ m=>by field_simp;linear_combination g1 m+g3 m-b1 m*(hβ m-hα m)-b1 m*hα m) λ m=>by linear_combination g3 m-b1 m*(hβ m-hα m))
 . have:=sub_ne_zero.2 hab;exact v0 (PS v d ((γ1-γ2)/(α-β)) (α*((γ1-γ2)/(α-β))-γ1) sv (λ m=>by field_simp;linear_combination g1 m-g2 m-v m*(hα m-hβ m)) λ m=>by field_simp;linear_combination β*g1 m-α*g2 m+v m*(α*hβ m-β*hα m))
lemma ZO {p q t0 t1 t2 t3:qi} (hp:p∈qB L 3) (hq:qo 0 0 q 0∈L) (hT:qo t0 t1 t2 t3∈L) (sp:zL p=0) (sq:zL q=0) (dpq:zr p q=0):qp p q t0+qp p q t1=0:=by
 have h1:=(v5 hL hp (x:=![1,1,1+q,1]) (t:=![t0,t1,t2,t3]) (by have:=(zP L).add_mem vZ (mem_sup_left hq);rwa[jw.2.2.2.2.1,add_zero] at this) hT).1
 have h2:=(v5 hL hp (x:=λ _=>1) (t:=![t0,t1,t2,t3]) vZ hT).1;simp[z8] at h1 h2
 have e:qa p t0 1 q+qa p 1 t1 q=0:=by simp only[qa,qN] at h1 h2 ⊢;linear_combination h1-h2
 rw[ky.2.2.2.1,ky.2.2.2.2] at e;simp only[qW,sp,sq,dpq] at e;simp only[qp] at e ⊢;linear_combination e/2
lemma Ys {p v0 v1 v2 w0 w1 w2 w3:qi} (Mp:qo 0 0 0 p∈L) (A1:qo v0 (-v1) 0 0∈L) (A2:qo v0 0 (-v2) 0∈L) (S0:qo w0 0 0 (-w3)∈L) (B1:qo w0 (-w1) 0 0∈L) (B2:qo w0 0 (-w2) 0∈L) (sv:zL v0=0) (sw:zL w0=1):zL v1=0/\zL v2=0/\zL w1=1/\zL w2=1/\zr v0 v1=0/\zr v0 v2=0/\zr v1 v2=0/\qp v0 v1 v2=0/\zr p v1=zr p v0/\zr p v2=zr p v0/\zr p w0=0/\zr p w1=0/\zr p w2=0/\zr w0 w1=1/\qp w0 w1 w2=1/\zr v0 w1+zr v1 w0=0:=by
 have hp:yu 3 p∈L:=yK.2.2.2.2 Mp;have sp:=yz hL hp
 have S1:qo 0 w1 0 (-w3)∈L:=by simpa using qh S0 B1 1 (-1)
 have S2:qo 0 0 w2 (-w3)∈L:=by simpa using qh S0 B2 1 (-1)
 have c1:=y8 hL A1;have c2:=y8 hL A2;have c3:=y8 hL S0;have c4:=y8 hL B1;have c5:=y8 hL B2;have c6:=y8 hL (qh B1 B2 1 (-1));have c7:=y8 hL (qh B1 B2 1 1);have e12:=y8 hL (qh A1 A2 1 (-1));have f12:=y8 hL (qh A1 A2 1 1);have m1:=y8 hL (qh A1 B1 1 1)
 have q1:=(qR hL hp A1).2.1;have q2:=(qR hL hp A2).2.1;have q3:=(qR hL hp S0).2.1;have q4:=(qR hL hp S1).2.1;have q5:=(qR hL hp S2).2.1
 simp only[z8,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_three] at q1 q2 q3 q4 q5
 simp only[zL,wv,qW,zr,qp,qa,qN] at c1 c2 c3 c4 c5 c6 c7 e12 f12 m1 q1 q2 q3 q4 q5 sv sw sp ⊢
 obtain ⟨c1a,c1b,-,-⟩:=c1;obtain ⟨c2a,c2b,-,-⟩:=c2;obtain ⟨c3a,-,-,-⟩:=c3;obtain ⟨c4a,c4b,-,-⟩:=c4;obtain ⟨c5a,c5b,-,-⟩:=c5;obtain ⟨-,c6b,-,-⟩:=c6;obtain ⟨-,-,c7c,-⟩:=c7;obtain ⟨-,e12b,-,-⟩:=e12;obtain ⟨-,-,f12c,-⟩:=f12;obtain ⟨-,m1b,-,-⟩:=m1
 and_intros<;>grind
lemma Yu {p v0 v1 v2 w0 w1 w2 w3:qi} (Mp:qo 0 0 0 p∈L) (A1:qo v0 (-v1) 0 0∈L) (A2:qo v0 0 (-v2) 0∈L) (S0:qo w0 0 0 (-w3)∈L) (B1:qo w0 (-w1) 0 0∈L) (B2:qo w0 0 (-w2) 0∈L):PX p v0 v1 v2 w0 w1 w2:=by
 have hp:yu 3 p∈L:=yK.2.2.2.2 Mp
 have S1:qo 0 w1 0 (-w3)∈L:=by simpa using qh S0 B1 1 (-1)
 have S2:qo 0 0 w2 (-w3)∈L:=by simpa using qh S0 B2 1 (-1)
 have Q:=λ {a b c d:qi} (h:qo a b c d∈L)=>(qR hL hp h).2.2
 have q1:=(Q A1).1;have q2:=(Q A2).1;have q3:=(Q (qh A1 A2 1 1)).1;have q4:=(Q (qh A1 A2 1 (-1))).1;have q5:=(Q (qh S0 S1 1 1)).1;have q6:=(Q (qh S0 S2 1 1)).1;have q7:=(Q (qh S1 S2 1 1)).1;have q8:=(Q (qh A1 S1 1 1)).1;have q9:=(Q (qh A2 S2 1 1)).1;have q10:=(Q (qh A1 S0 1 1)).1;have q11:=(Q (qh A2 S0 1 1)).1;have q12:=(Q (qh A1 S2 1 1)).1;have q13:=(Q (qh A2 S1 1 1)).1
 have r0:=(Q (qh A1 A2 1 1)).2;have r1:=(Q (qh (qh S0 S1 1 1) S2 1 1)).2;have r2:=(Q (qh (qh S0 S1 1 1) A2 1 1)).2;have r3:=(Q (qh S1 A2 1 1)).2;have r4:=(Q (qh (qh S0 S2 1 1) A1 1 1)).2;have r5:=(Q (qh S2 A1 1 1)).2;have r6:=(Q (qh (qh S1 S2 1 1) A1 1 1)).2;have r7:=(Q (qh S0 (qh A1 A2 1 (-1)) 1 1)).2
 simp only[z8,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_three] at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 r0 r1 r2 r3 r4 r5 r6 r7
 simp only[PX,qW,zL,zr,qp,qa,qN] at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 r0 r1 r2 r3 r4 r5 r6 r7 ⊢
 exact ⟨by linear_combination -q1,by linear_combination -q2,by linear_combination -q4,by linear_combination q5,by linear_combination q6,by linear_combination q7,by linear_combination q8-q1,by linear_combination q9-q2,by linear_combination -q10+q1,by linear_combination -q12+q1+q9-q2,by linear_combination -q11+q2,by linear_combination -q13+q8-q1+q2,by linear_combination r0/2,by linear_combination r1,by linear_combination -r2+r3,by linear_combination -r4+r5,by linear_combination r6-r5,by linear_combination -r7,by linear_combination -r3,by linear_combination -r5⟩
lemma Yv {v w:qi} (hv:v∈qB L 2) (hw:qo 0 0 0 w∈L) {x0 x1 x2 x3:qi} (hX:qo x0 x1 x2 x3∈zP L):qa x0 x1 v w=0:=by
 have:=(v5 hL hv (x:=![x0,x1,x2,x3]) (t:=![0,0,0,w]) hX hw).1;simp[z8] at this;simp only[qa] at this ⊢;linear_combination this
section
variable (h6:finrank KD L=6)
include h6
lemma Yw (n0:finrank KD (qH L 0)=1) (n1:finrank KD (qH L 1)=2) (n2:finrank KD (qH L 2)=2) (n3:finrank KD (qH L 3)=2) (p1:finrank KD (qB L 1)=1) (p2:finrank KD (qB L 2)=1):False:=by
 obtain ⟨a,ha,a0⟩:=wR p1;obtain ⟨b,hb,b0⟩:=wR p2;have sa:=yz hL ha
 have P:∀ {i j l m:Fin 4},k5 j i l m-> finrank KD (qH L j)+finrank KD (qB L i)+finrank KD (qH L l)+finrank KD (qH L m)≤6-> ∀ {p},p∈qB L i-> ∀ u∈qH L j,zr p u=0:=λ D d p hp u hu=>by obtain ⟨w,hw⟩:=js _ _ _ _ (h6▸d) hu D;exact Yq hL (Ne.symm D.1) hp (add_comm (yu _ u) _▸hw)
 have a3:=P (i:=1) (j:=3) (l:=0) (m:=2) (by decide) (by omega) ha
 obtain ⟨μ,rfl⟩:=wy (qg hL 3) n3 a0 sa (yz hL hb) a3 (P (i:=2) (j:=3) (l:=0) (m:=1) (by decide) (by omega) hb)
 have μ0:μ≠0:=by rintro rfl;simp at b0
 have daa:zr a a=0:=by simpa[yY,μ0] using P (i:=1) (j:=2) (l:=0) (m:=3) (by decide) (by omega) ha _ (wg hb)
 refine PR (qg hL 3) n3 a0 sa daa a3 λ u hu=>?_
 obtain ⟨w,hw⟩:=js 3 1 0 2 (by omega) hu;simp only[jw] at hw
 have h1:=(v5 hL ha (x:=![1,1,1+μ•a,1]) (t:=![0,w,0,u]) (by have:=(zP L).add_mem vZ (mem_sup_left (yK.2.2.1.1 hb));rwa[jw.2.2.2.2.1,add_zero] at this) hw).1
 have h2:=(v5 hL ha (x:=λ _=>1) (t:=![0,w,0,u]) vZ hw).1;simp[z8] at h1 h2
 have e:qa a 1 (μ•a) u=0:=by simp only[qa,qN] at h1 h2 ⊢;linear_combination h1-h2
 rw[ky.2.2.2.2] at e;simp[qW,sa,yY,daa,μ0] at e;simpa[zr,qp,mul_comm,mul_left_comm] using e
lemma Jg {r a b:Fin 4} (hab:a≠b) (hv:yu r (Pi.single a 1-Pi.single b 1)∈L) (hrow:∀ T∈L,∀ k,k≠r-> T (k,a)=T (k,b)):False:=by
 obtain ⟨σ,h1,h2⟩:=(by decide:∀ a b:Fin 4,a≠b-> ∃ σ:Equiv.Perm (Fin 4),σ 1=a/\σ 2=b) a b hab
 have ia:∀ i,σ i=a↔ i=1:=λ i=>⟨λ e=>σ.injective (e.trans h1.symm),λ e=>e▸h1⟩
 have ib:∀ i,σ i=b↔ i=2:=λ i=>⟨λ e=>σ.injective (e.trans h2.symm),λ e=>e▸h2⟩
 have it:∀ j,Equiv.swap 0 r j=r↔ j=0:=λ j=>by rw[← Equiv.swap_apply_left 0 r];exact (Equiv.swap 0 r).injective.eq_iff
 refine yR (zH (zX hL) σ (Equiv.swap 0 r)) ((zF _ σ _).trans ((zT L).trans h6)) ⟨_,⟨_,hv,rfl⟩,funext λ ⟨i,j⟩=>?_⟩ ?_
 . simp only[LinearEquiv.coe_coe,zy,zQ,yu,LinearMap.coe_mk,AddHom.coe_mk,Pi.sub_apply,Pi.single_apply,it,ia,ib,Prod.mk.injEq];fin_cases i<;>fin_cases j<;>simp
 . rintro _ ⟨_,⟨T,hT,rfl⟩,rfl⟩ j hj;simp only[LinearEquiv.coe_coe,zy,zQ,h1,h2];exact hrow T hT _ λ e=>hj ((it j).1 e)
lemma Jh {j:Fin 4} (h3:finrank KD (L.map (zD j))=3) {m:(Fin 4-> KD) →ₗ[KD] KD} (hm:∀ a,∀ T∈L,m (λ i=>a+T (i,j))=a) {r:Fin 4} {p:Fin 4-> KD} (hp:yu r p∈L) (p0:p≠0):m (Pi.single r 1)=0:=by
 by_contra hi;by_cases hpj:p j=0
 . suffices e:yu r p=0 from p0 (funext λ c=>by simpa[yu] using congrFun e (r,c))
   refine (Submodule.eq_bot_iff _).1 (qS hL h6 h3 hm hi) _ ⟨⟨hp,mem_ker.2 (funext λ i=>?_)⟩,mem_ker.2 (funext λ a=>funext λ b=>?_)⟩
   . simp only[qF,yu,LinearMap.coe_mk,AddHom.coe_mk,Pi.zero_apply];split_ifs<;>simp[hpj]
   . simp only[zt,yu,LinearMap.coe_mk,AddHom.coe_mk,Pi.zero_apply];rw[ite_eq_right_iff];intro h;exfalso;revert h;fin_cases a<;>fin_cases r<;>decide
 have:=hm 0 _ hp
 rw[show (λ i=>(0:KD)+yu r p (i,j))=p j•Pi.single r 1 from funext λ i=>by simp only[yu,LinearMap.coe_mk,AddHom.coe_mk,zero_add,Pi.smul_apply,Pi.single_apply,smul_eq_mul];split_ifs<;>simp,map_smul,smul_eq_mul] at this
 exact hi ((mul_eq_zero.1 this).resolve_left hpj)
lemma ZP {v w:Fin 4-> KD} (hv:v∈qB L 2) (v0:v≠0) (hw:w∈qB L 3) (w0:w≠0) {i:Fin 4} {T T' d:ze} (hT:T∈L) (hT':T'∈L) (hd:d∈L) (hdet:T (0,i)*T' (1,i)-T (1,i)*T' (0,i)≠0) (hd0:d (0,i)=0) (hd1:d (1,i)=0) {k:Fin 4} (hdk:d (k,i)≠0):False:=by
 have li:LinearIndependent KD ![zD i T,zD i T',zD i d]:=vJ _ ![proj 0,proj 1,proj k] (by
  simp only[Matrix.det_fin_three,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,LinearMap.proj_apply,qF,hd0,hd1]
  intro h;apply hdet;exact (mul_eq_zero.1 (by linear_combination h:d (k,i)*(T (0,i)*T' (1,i)-T (1,i)*T' (0,i))=0)).resolve_left hdk)
 have h3:finrank KD (L.map (zD i))=3:=le_antisymm (k9 hL i) (by
  have e:=finrank_span_eq_card li;simp only[Fintype.card_fin] at e
  have:=finrank_mono (show span KD (Set.range ![zD i T,zD i T',zD i d])≤L.map (zD i) from span_le.2 (by rintro _ ⟨a,rfl⟩;fin_cases a;exacts[⟨T,hT,rfl⟩,⟨T',hT',rfl⟩,⟨d,hd,rfl⟩]));omega)
 obtain ⟨l,hl,-⟩:=(j3 hL h3).2
 have i2:=Jh hL h6 h3 hl hv v0;have i3:=Jh hL h6 h3 hl hw w0
 have dec:∀ x:Fin 4-> KD,l x=x 0*l (Pi.single 0 1)+x 1*l (Pi.single 1 1)+x 2*l (Pi.single 2 1)+x 3*l (Pi.single 3 1):=λ x=>by
  conv_lhs=>rw[show x=x 0•Pi.single 0 1+x 1•Pi.single 1 1+x 2•Pi.single 2 1+x 3•Pi.single 3 1 by funext m;fin_cases m<;>simp]
  simp only[map_add,map_smul,smul_eq_mul]
 have e1:=hl 1 0 L.zero_mem;have e2:=hl 0 T hT;have e3:=hl 0 T' hT';simp only[Pi.zero_apply,add_zero,zero_add] at e1 e2 e3;rw[dec,i2,i3] at e1 e2 e3
 apply hdet;by_contra hne
 have z0:=(mul_eq_zero.1 (by linear_combination T' (1,i)*e2-T (1,i)*e3:l (Pi.single 0 1)*(T (0,i)*T' (1,i)-T (1,i)*T' (0,i))=0)).resolve_right hne
 have z1:=(mul_eq_zero.1 (by linear_combination T (0,i)*e3-T' (0,i)*e2:l (Pi.single 1 1)*(T (0,i)*T' (1,i)-T (1,i)*T' (0,i))=0)).resolve_right hne
 rw[z0,z1] at e1;norm_num at e1
lemma ZQ {i:Fin 4} {v:qi} (hv:yu i v∈L) (v0:v≠0) (sv:zL v=0) (hU:∀ k,k≠i-> ∀ u∈qH L k,zr v u=0) {x y:Fin 4} (hxy:x≠y) (hm:∀ m,m≠x-> m≠y-> v m=0):False:=by
 obtain ⟨c,d,D⟩:=xl x y hxy;obtain ⟨ev,dv⟩:=J6 D sv (hm c (Ne.symm D.2.1) (Ne.symm D.2.2.2.1)) (hm d (Ne.symm D.2.2.1) (Ne.symm D.2.2.2.2.1))
 have vx0:v x≠0:=λ h=>v0 (by rw[ev,h,zero_smul])
 set ζ:=v x
 have hv':yu i (Pi.single x 1-Pi.single y 1)∈L:=by have:yu i (ζ⁻¹•v)∈L:=(by rw[map_smul];exact L.smul_mem _ hv);rwa[ev,smul_smul,inv_mul_cancel₀ vx0,one_smul] at this
 exact Jg hL h6 hxy hv' λ T hT k hk=>sub_eq_zero.1 ((mul_eq_zero.1 ((dv _).symm.trans (hU k hk _ ⟨T,hT,rfl⟩))).resolve_left vx0)
section
variable (n:∀ i,finrank KD (qH L i)=2)
include n
lemma Yx (p:∀ i,finrank KD (qB L i)=0):False:=by
 obtain ⟨v,hv,v0,sv⟩:=Wj (n 0).ge
 obtain ⟨b1,h1⟩:=js 0 1 2 3 (by simp[n,p,h6]) hv;obtain ⟨b2,h2⟩:=js 0 2 1 3 (by simp[n,p,h6]) hv;obtain ⟨b3,h3⟩:=js 0 3 1 2 (by simp[n,p,h6]) hv
 have z:∀ {i b},yu 0 v+yu i b∈L-> b≠0:=λ h e=>by rw[e,map_zero,add_zero] at h;exact v0 (ki (p 0) h)
 have z1:=z h1;have z2:=z h2;have z3:=z h3;simp only[jw] at h1 h2 h3
 obtain ⟨s1,s2,s3,d1,d2,d3,d12,d13,d23,t12,t13,t23,t123,hP⟩:=Yr hL h1 h2 h3 sv
 exact ZC sv s1 s2 s3 d1 d2 d3 d12 d13 d23 t12 t13 t23 t123 hP v0 z1 z2 z3
lemma Yy (p0:finrank KD (qB L 0)=0) (p1:finrank KD (qB L 1)=0) (p2:finrank KD (qB L 2)=0) (p3:finrank KD (qB L 3)=2):False:=by
 obtain ⟨v,hv,v0,sv⟩:=Wj (n 0).ge;obtain ⟨b1,h1⟩:=js 0 1 2 3 (by simp[n,p1,h6]) hv;obtain ⟨b2,h2⟩:=js 0 2 1 3 (by simp[n,p2,h6]) hv
 have z1:b1≠0:=λ e=>by rw[e,map_zero,add_zero] at h1;exact v0 (ki p0 h1)
 simp only[jw] at h1 h2;exact Jf hL p3 h1 h2 sv v0 z1
lemma Ji (p0:finrank KD (qB L 0)=0) (p1:finrank KD (qB L 1)=0) (p2:finrank KD (qB L 2)=1) (p3:finrank KD (qB L 3)=2):False:=by
 obtain ⟨q,hq,q0⟩:=wR p2;have sq:=yz hL hq;have Mq:=yK.2.2.1.1 hq
 have spn:qB L 2=span KD {q}:=(wP ((span_singleton_le_iff_mem _ _).2 hq) (by rw[p2,finrank_span_singleton q0])).symm
 have dqp:∀ p∈qB L 3,zr p q=0:=λ p hp=>by simpa[z8] using (qR hL hp Mq).2.1
 have Dq:=Y8 (vL hL 3) p3.ge sq dqp q0
 by_cases hs:∀ u∈qH L 2,zL u=0
 . obtain ⟨v,hv,hvn⟩:=IsConcreteLE.exists_of_lt (lt_of_le_of_ne (spn▸wg) λ e=>by have:=n 2;rw[← e,finrank_span_singleton q0] at this;omega)
   obtain ⟨a0,h0⟩:=js 2 0 1 3 (by simp[n,p0,h6]) hv;obtain ⟨a1,h1⟩:=js 2 1 0 3 (by simp[n,p1,h6]) hv
   have z:∀ {i b},yu 2 v+yu i b∈L-> b≠0:=λ h e=>by rw[e,map_zero,add_zero] at h;exact hvn (spn▸h)
   have z0:=z h0;have z1:=z h1;simp only[jw] at h0 h1
   exact Jf hL p3 (by simpa using qh h0 h1 1 (-1)) h0 (by simpa[hs v hv] using (y8 hL h0).1) z0 (neg_ne_zero.2 z1)
 push Not at hs;obtain ⟨u,hu,su⟩:=hs
 obtain ⟨w,hw,sw⟩:∃ w∈qH L 2,zL w=1:=⟨_,smul_mem _ (zL u)⁻¹ hu,by simp[yY,su]⟩
 obtain ⟨a0,h0⟩:=js 2 0 1 3 (by simp[n,p0,h6]) hw;obtain ⟨a1,h1⟩:=js 2 1 0 3 (by simp[n,p1,h6]) hw;simp only[jw] at h0 h1
 have sa0:zL a0= -1:=by have:=(y8 hL h0).1;simp[sw] at this;linear_combination this
 have sa1:zL a1= -1:=by have:=(y8 hL h1).1;simp[sw] at this;linear_combination this
 obtain ⟨v,hv,v0,sv⟩:=Wj (n 0).ge;obtain ⟨b,hb⟩:=js 0 1 2 3 (by simp[n,p1,h6]) hv;simp only[jw] at hb
 have c:=y8 hL hb;simp[sv,wv] at c;obtain ⟨sb,dvb⟩:=c
 have A:=λ p (hp:p∈qB L 3)=>wW hL hp hb sv sb gaz.1
 obtain ⟨c,hc⟩:=Dq (v+b) (by simp[yY,sv,sb]) λ p hp=>by simpa[yY] using (A p hp).1
 have dqvb:zr q (v+b)=0:=by simpa[z8,yY] using (qR hL hq hb).2.1
 obtain ⟨e,he⟩:=Dq (v*b) (by simpa[zL,zr] using dvb) λ p hp=>by simpa[zr,qp,mul_assoc] using (A p hp).2.1
 have tqvb:qp q v b=0:=by have:=(qR hL hq hb).2.2.1;simp[z8,qW,sq,sv,sb] at this;exact this
 simp only[qN] at hc he
 have vz:(∀ i,v i*v i=0)-> False:=λ h=>v0 (funext λ i=>by simpa using h i)
 by_cases hqq:zr q q=0
 . obtain rfl:c=0:=by
     by_contra c0
     obtain ⟨κ,hκ⟩:=Dq (q*q) (by simpa[zL,zr] using hqq) λ p hp=>by
       have:qp p q v+qp p q b=c*zr p (q*q):=by simp only[qp,zr,qN];linear_combination p 0*q 0*hc 0+p 1*q 1*hc 1+p 2*q 2*hc 2+p 3*q 3*hc 3
       rw[ZO hL hp Mq hb (yz hL hp) sq (dqp p hp)] at this;exact (mul_eq_zero.1 this.symm).resolve_left c0
     exact ZD q q0 sq κ (by simpa using hκ)
   obtain rfl:b=-v:=funext λ i=>by simp only[qN];linear_combination hc i
   simp only[qN] at he
   have dvv:zr v v=0:=by simpa[yY] using dvb
   have e0:e≠0:=λ h=>vz λ i=>by have:=he i;simp only[h] at this;linear_combination -this
   have pq:∀ x,(∀ p∈qB L 3,zr p x=0)-> ∃ f g:KD,∀ m,x m=f+g*q m:=λ x hx=>by
     obtain ⟨g,hg⟩:=Dq (x-(zL x/4)•1) (by simp only[zL,qN];ring) λ p hp=>by have a:=hx p hp;have b:=yz hL hp;simp only[zr,zL,qN] at a b ⊢;linear_combination a-(x 0+x 1+x 2+x 3)/4*b
     exact ⟨zL x/4,g,λ m=>by have:=hg m;simp only[qN] at this;linear_combination this⟩
   obtain ⟨f0,g0,b0⟩:=pq (q*a0) λ p hp=>by simpa[zr,qp,mul_assoc] using ZO hL hp Mq h0 (yz hL hp) sq (dqp p hp)
   obtain ⟨f1,g1,b1⟩:=pq (q*a1) λ p hp=>by simpa[zr,qp,mul_assoc] using ZO hL hp Mq h1 (yz hL hp) sq (dqp p hp)
   have h01:qo a0 (-a1) 0 0∈L:=by simpa using qh h0 h1 1 (-1)
   have dd:zr a0 a1=1:=by have:=(y8 hL h01).2.1;simp[wv,yY,sa0,sa1] at this;linear_combination this
   obtain ⟨f2,g2,ee⟩:=pq (λ m=>a0 m+a1 m+2*a0 m*a1 m) λ p hp=>by
     have c:=(qR hL hp h01).2.2.1;have sp:=yz hL hp;simp[z8] at c;simp only[qW,zL,zr,qp,qN] at c sp sa0 sa1 ⊢;grind
   have F:=λ z y:KD=>(Yo hL (by have:=(zP L).add_mem ((zP L).add_mem vZ ((zP L).smul_mem z (mem_sup_left Mq))) ((zP L).smul_mem y (mem_sup_left hb));simpa[jw] using this:qo (1+y•v) (1+y•(-v)) (1+z•q) 1∈zP L) h0).1
   have key:qa a0 (-v) q 1=0:=by have f1:=F 1 1;have f2:=F 1 0;have f3:=F 0 1;have f4:=F 0 0;simp only[qa,qN] at f1 f2 f3 f4 ⊢;linear_combination f1-f2-f3+f4
   rw[ky.2.2.1] at key;simp[qW,yY,sv,sq,sa0] at key
   exact Yc v a0 a1 q (-1/e) f0 g0 f1 g1 f2 g2 sv dvv (λ i=>by have:=he i;field_simp;linear_combination -this) (by simp[e0]) hqq sa0 sa1 b0 b1 dd ee (by linear_combination -key) v0
 have c0:c*zr q q=0:=by simp only[zr,qN] at dqvb ⊢;linear_combination dqvb-(q 0*hc 0+q 1*hc 1+q 2*hc 2+q 3*hc 3)
 have e0:e*zr q q=0:=by simp only[zr,qp] at tqvb ⊢;linear_combination tqvb-(q 0*he 0+q 1*he 1+q 2*he 2+q 3*he 3)
 simp[hqq] at c0 e0;subst c0 e0;exact vz λ i=>by linear_combination -he i+v i*hc i
lemma Yz (p0:finrank KD (qB L 0)=0) (p1:finrank KD (qB L 1)=0) (p2:finrank KD (qB L 2)=0) (p3:finrank KD (qB L 3)=1):False:=by
 obtain ⟨p,hp,pz⟩:=wR p3;have sp:=yz hL hp;have Mp:=yK.2.2.2.1 hp
 have l2:∀ {v},v∈qH L 0-> ∃ b1 b2,qo v (-b1) 0 0∈L/\qo v 0 (-b2) 0∈L:=λ hv=>by
  obtain ⟨b1,h1⟩:=js 0 1 2 3 (by simp[n,p1,h6]) hv;obtain ⟨b2,h2⟩:=js 0 2 1 3 (by simp[n,p2,h6]) hv;simp only[jw] at h1 h2;exact ⟨-b1,-b2,by simpa,by simpa⟩
 by_cases easy:∃ v∈qH L 0,v≠0/\zL v=0/\zr p v=0
 . obtain ⟨v,hv,v0,sv,pv⟩:=easy;obtain ⟨b1,b2,h1,h2⟩:=l2 hv
   have z1:-b1≠0:=λ e=>v0 (ki p0 (by rw[jw.1];simpa[e] using h1))
   have z2:-b2≠0:=λ e=>v0 (ki p0 (by rw[jw.1];simpa[e] using h2))
   obtain ⟨s1,s2,d1,d2,d12,t12⟩:=Je hL h1 h2 sv
   have A:=wW hL hp h1 sv s1 gaz.1;have B:=wW hL hp h2 sv gaz.1 s2
   have C:=wW hL hp (by simpa using qh h1 h2 1 (-1):qo 0 (-b1) b2 0∈L) gaz.1 s1 (by simpa[yY] using s2)
   have E:=wW hL hp (by simpa using qh h1 h2 1 1:qo (v+v) (-b1) (-b2) 0∈L) (by simp[yY,sv]) s1 s2
   exact ZC sv s1 s2 sp d1 d2 (by rw[qO];exact pv) d12 (by rw[qO];simpa[pv] using A.1) (by rw[qO];simpa[pv] using B.1) t12 (by have:=A.2.1;simp only[qp,qN] at this ⊢;linear_combination this) (by have:=B.2.1;simp only[qp,qN] at this ⊢;linear_combination this) (by have:=C.2.1;simp only[qp,qN] at this ⊢;linear_combination -this) (by have:=E.2.2;simp only[qa,qN] at this ⊢;linear_combination this/2) v0 z1 z2 pz
 push Not at easy
 obtain ⟨v0,hv0,vz,sv⟩:=Wj (n 0).ge;have π0:=easy v0 hv0 vz sv;obtain ⟨v1,v2,A1,A2⟩:=l2 hv0
 obtain ⟨x,y,x0,hx⟩:=kZ (L:=L) 0 3 1 2 (by simp[n,p3,h6]);simp only[jw] at hx
 have hxU:x∈qH L 0:=⟨_,hx,rfl⟩
 have sx:zL x≠0:=λ h=>easy x hxU x0 h (by simpa[z8] using (qR hL hp hx).2.1)
 obtain ⟨w1,w2,B1,B2⟩:=l2 (smul_mem _ (zL x)⁻¹ hxU)
 have S0:qo ((zL x)⁻¹•x) 0 0 (-(-((zL x)⁻¹•y)))∈L:=by simpa[jw] using L.smul_mem (zL x)⁻¹ hx
 have u0:zL ((zL x)⁻¹•x)=1:=by simp[yY,sx]
 obtain ⟨s1,s2,u1,u2,d01,d02,d12,t012,f1,f2,e0,e1,e2,ww,www,vw⟩:=Ys hL Mp A1 A2 S0 B1 B2 sv u0
 have G:=Yu hL Mp A1 A2 S0 B1 B2
 set w0:=(zL x)⁻¹•x
 set π:=zr p v0
 have f0:zr p v0=π:=rfl
 have T:∀ {a b},qW p a b=0-> qW p b a=0:=λ h=>by rw[← h];simp only[qW,zL,zr,qp];ring
 by_cases hz:∃ m,p m=0
 . obtain ⟨m,pm⟩:=hz
   by_cases hz2:∃ m',m'≠m/\p m'=0
   . obtain ⟨m',hm',pm'⟩:=hz2
     have tt:∀ a b:qi,zL a=0-> zL b=0-> qW p a b=0-> qp p a b=0:=λ a b ha hb h=>by simp only[qW,sp,ha,hb] at h;linear_combination h/2
     obtain ⟨g1,g2,g3,-,-,-,-,-,-,-,-,-,g13,-⟩:=G
     exact PW p v0 v1 v2 _ π0 sp (hm'.symm) pm pm' sv s1 s2 d01 d02 d12 (tt _ _ sv s1 g1) (tt _ _ sv s2 g2) (tt _ _ s1 s2 g3) rfl f1 f2 g13
   push Not at hz2
   obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,-,-,c3,c4,c5,-⟩:=G
   have D01:=ZF p v0 w0 v1 w1 m π π0 sp pm hz2 sv f0 u0 e0 s1 f1 u1 e1 b1 b7 (T b9) b4
   have D02:=ZF p v0 w0 v2 w2 m π π0 sp pm hz2 sv f0 u0 e0 s2 f2 u2 e2 b2 b8 (T b11) b5
   have D12:=ZF p v1 w1 v2 w2 m π π0 sp pm hz2 s1 f1 u1 e1 s2 f2 u2 e2 b3 b10 (T b12) b6
   have fin:∀ v,zr p v=π-> qa p ((1/2:KD)•wS m) ((1/2:KD)•wS m) v≠0:=λ v hv h=>by
    have e:=(ZE p m sp pm v).2.2.2
    have:qa p ((1/2:KD)•wS m) ((1/2:KD)•wS m) v=qa p (wS m) (wS m) v/4:=by simp only[qa,qN];ring
    rw[this,e,hv] at h;exact π0 (by linear_combination 2*h)
   have P1:∀ a b c:qi,qa p a b c=qa p a c b/\qa p a b c=qa p b c a:=λ a b c=>by simp only[qa];constructor<;>ring
   rcases D01 with h0|h1
   . rcases D12 with h1|h2
     . rw[h0,h1] at c3;exact fin v2 f2 c3
     . rw[h0,h2,(P1 _ _ _).1] at c4;exact fin v1 f1 c4
   . rcases D02 with h0|h2
     . rw[h0,h1] at c3;exact fin v2 f2 c3
     . rw[h1,h2,(P1 _ _ _).2] at c5;exact fin v0 f0 c5
 push Not at hz
 obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,-,c2,-⟩:=G
 have h1:=(xg p v0 w0 v1 v2 w2 π π0 sp hz sv u0 f0 e0 s2 f2 u2 e2 b2 b8 (T b11) b5 b3 b10).1 s1 f1
 have h2:=(xg p v0 w0 v2 v1 w1 π π0 sp hz sv u0 f0 e0 s1 f1 u1 e1 b1 b7 (T b9) b4 (T b3) b12).1 s2 f2
 have h3:=(xg p v0 w0 w1 v2 w2 π π0 sp hz sv u0 f0 e0 s2 f2 u2 e2 b2 b8 (T b11) b5 (T b12) b6).2 u1 e1
 have h4:=(xg p v0 w0 w2 v1 w1 π π0 sp hz sv u0 f0 e0 s1 f1 u1 e1 b1 b7 (T b9) b4 (T b10) (T b6)).2 u2 e2
 subst v1 v2 w1 w2;exact Ye p w0 sp hz u0 e0 b4 c2 ww www
lemma Jj (p0:finrank KD (qB L 0)=0) (p1:finrank KD (qB L 1)=0) (p2:finrank KD (qB L 2)=1) (p3:finrank KD (qB L 3)=1):False:=by
 obtain ⟨v,hv,v0⟩:=wR p2;obtain ⟨w,hw,w0⟩:=wR p3;have sv:=yz hL hv;have sw:=yz hL hw;have Mv:=yK.2.2.1.1 hv;have Mw:=yK.2.2.2.1 hw
 have dvw:zr v w=0:=by simpa[z8] using (qR hL hv Mw).2.1
 have QQ:=λ {x0 x1 x2 x3:qi} (h:qo x0 x1 x2 x3∈zP L)=>Yv hL hv Mw h
 have m0:∀ {a b c d:qi},qo a b c d∈L-> a∈qH L 0:=λ h=>⟨_,h,rfl⟩
 have l01:∀ u∈qH L 0,∃ b,qo u b 0 0∈L:=λ u hu=>by obtain ⟨b,hb⟩:=js 0 1 2 3 (by simp[n,p1,h6]) hu;simp only[jw] at hb;exact ⟨b,hb⟩
 have l10:∀ y∈qH L 1,∃ a,qo a y 0 0∈L:=λ y hy=>by obtain ⟨a,ha⟩:=js 1 0 2 3 (by simp[n,p0,h6]) hy;simp only[jw] at ha;exact ⟨a,ha⟩
 obtain ⟨x2,y2,x20,S2⟩:=kZ (L:=L) 0 2 1 3 (by simp[n,p2,h6]);simp only[jw] at S2
 obtain ⟨x3,y3,x30,S3⟩:=kZ (L:=L) 0 3 1 2 (by simp[n,p3,h6]);simp only[jw] at S3
 have P1t:∀ x,qa x 1 v w=2*qp x v w/\qa 1 x v w=2*qp x v w:=λ x=>by simp only[qa,qp,zL,zr,qN] at sv sw dvw ⊢;constructor<;>grind
 have tU:∀ {a b c d:qi},qo a b c d∈L-> qp a v w+qp b v w=0:=λ {a b c d} h=>by
  have e1:=QQ (by have:=(zP L).add_mem vZ (mem_sup_left h);rwa[jw.2.2.2.2.1] at this);have e2:=QQ (vZ (L:=L));have e3:=QQ (mem_sup_left h)
  have:qa a 1 v w+qa 1 b v w=0:=by simp only[qa,qN] at e1 e2 e3 ⊢;linear_combination e1-e2-e3
  rw[(P1t a).1,(P1t b).2] at this;linear_combination this/2
 have tU0:∀ {a c d:qi},qo a 0 c d∈L-> qp a v w=0:=λ h=>by simpa using tU h
 have tU1:∀ {b c d:qi},qo 0 b c d∈L-> qp b v w=0:=λ h=>by simpa using tU h
 have hCI:∀ i,(v i≠0\/w i≠0)-> ∀ {a c d a' c' d':qi},qo a 0 c d∈L-> qo 0 a' c' d'∈L-> a i*a' i=0:=λ i hi a c d a' c' d' hT hT'=>by
  by_contra hne;rcases hi with hi|hi
  . exact ZP hL h6 hv v0 hw w0 hT hT' Mv (k:=2) (by simpa[qo] using hne) rfl rfl hi
  . exact ZP hL h6 hv v0 hw w0 hT hT' Mw (k:=3) (by simpa[qo] using hne) rfl rfl hi
 by_cases hB:∃ c:KD,x3=c•x2
 . obtain ⟨c,rfl⟩:=hB;have c0:c≠0:=by rintro rfl;simp at x30
   have Dl:qo 0 0 (-c•y2) y3∈L:=by simpa using qh S3 S2 1 (-c)
   obtain ⟨dD,wy2⟩:(∀ i,∃ d∈L,d (0,i)=0/\d (1,i)=0/\∃ k,d (k,i)≠0)/\zr w y2=0:=by
    have Mv:=yK.2.2.1.1 hv;have Mw:=yK.2.2.2.1 hw
    have nx:∀ {e:qi},qo e 0 0 0∈L-> e=0:=λ h=>ki p0 (yK.1.2 h)
    have hy2:∀ κ:KD,y2≠κ•v:=λ κ e=>x20 (nx (by simpa[e] using qh S2 Mv 1 (-κ)))
    have hy3:∀ κ:KD,y3≠κ•w:=λ κ e=>by
     obtain ⟨κ',hκ'⟩:=mem_span_singleton.1 ((wP ((span_singleton_le_iff_mem _ _).2 hv) (by rw[p2,finrank_span_singleton v0])).symm▸yK.2.2.1.2 (by simpa[e] using qh Dl Mw 1 (-κ)):-c•y2∈span KD {v})
     exact hy2 (-κ'/c) (funext λ m=>by have:=congrFun hκ' m;simp only[qN] at this ⊢;field_simp;first | linear_combination -this | linear_combination this)
    have U2:=wV (n 2) (wg hv) (⟨_,S2,rfl⟩:y2∈qH L 2) v0 hy2
    have U3:=wV (n 3) (wg hw) (⟨_,Dl,rfl⟩:y3∈qH L 3) w0 hy3
    have D2:∀ u∈qH L 2,∃ e,qo 0 0 u e∈L:=λ u hu=>by
     obtain ⟨a,b,rfl⟩:=U2 u hu;have h:=qh Mv Dl a (-b/c);simp only[smul_zero,add_zero,zero_add] at h
     rw[show a•v+(-b/c)•(-c•y2)=a•v+b•y2 by funext m;simp only[qN];field_simp] at h;exact ⟨_,h⟩
    have D3:∀ u∈qH L 3,∃ e,qo 0 0 e u∈L:=λ u hu=>by obtain ⟨a,b,rfl⟩:=U3 u hu;have h:=qh Mw Dl a b;simp only[smul_zero,add_zero,zero_add] at h;exact ⟨_,h⟩
    have wU2:∀ u∈qH L 2,zr w u=0:=λ u hu=>by obtain ⟨e,he⟩:=D2 u hu;simpa[z8] using (qR hL hw he).2.1
    have cov:∀ i,(∃ u∈qH L 2,u i≠0)\/∃ u∈qH L 3,u i≠0:=λ i=>by
     by_contra hc;push Not at hc;obtain ⟨z2,z3⟩:=hc;have wi:w i=0:=z3 w (wg hw)
     have ei:∀ y:qi,zr (Pi.single i 1) y=y i:=λ y=>by fin_cases i<;>simp[zr]
     have li:LinearIndependent KD ![Pi.single i (1:KD),w]:=(LinearIndependent.pair_iff' (by simp)).2 λ a e=>w0 (by have:=congrFun e i;simp[wi] at this;rw[← e,this,zero_smul])
     have hp:=xd (span KD (Set.range ![Pi.single i (1:KD),w])) (ker (proj i)⊓ker (wF w)) λ x hx y hy=>by
      obtain ⟨c,rfl⟩:=(kh KD).1 hx;have y1:y i=0:=hy.1;have y2:zr w y=0:=hy.2;simp[Fin.sum_univ_two,yY,ei,y1,y2]
     rw[finrank_span_eq_card li,Fintype.card_fin] at hp
     have hm:(1:Fin 4-> KD)-Pi.single i 1∈qH L 2:=by
      have le:qH L 2≤ker (proj i)⊓ker (wF w):=λ u hu=>⟨z2 u hu,wU2 u hu⟩
      rw[wP le (by rw[n 2];omega)]
      refine ⟨by simp,?_⟩;show zr w _=0;simp only[zL] at sw;fin_cases i<;>simp[zr] at wi ⊢<;>grind
     obtain ⟨e,he⟩:=D2 _ hm;have ei':e i=0:=z3 e ⟨_,he,rfl⟩;obtain ⟨c1,c2,-⟩:=y8 hL he
     simp only[zL,wv,zr,qN,Pi.single_apply] at c1 c2;fin_cases i<;>simp at c1 c2 ei'<;>grind
    refine ⟨λ i=>?_,wU2 y2 ⟨_,S2,rfl⟩⟩
    rcases cov i with ⟨u,hu,ui⟩|⟨u,hu,ui⟩
    . obtain ⟨e,he⟩:=D2 u hu;exact ⟨_,he,rfl,rfl,2,ui⟩
    . obtain ⟨e,he⟩:=D3 u hu;exact ⟨_,he,rfl,rfl,3,ui⟩
   have m0:∀ {a b c d:qi},qo a b c d∈L-> a∈qH L 0:=λ h=>⟨_,h,rfl⟩
   have m1:∀ {a b c d:qi},qo a b c d∈L-> b∈qH L 1:=λ h=>⟨_,h,rfl⟩
   have nx:∀ {e:qi},qo e 0 0 0∈L-> e=0:=λ h=>ki p0 (yK.1.2 h)
   have dz:∀ i {a b c d a' b' c' d':qi},qo a b c d∈L-> qo a' b' c' d'∈L-> a i*b' i-b i*a' i=0:=λ i a b c d a' b' c' d' h h'=>by obtain ⟨d0,hd,e0,e1,k,ek⟩:=dD i;by_contra hne;exact ZP hL h6 hv v0 hw w0 h h' hd (by simpa[qo] using hne) e0 e1 ek
   obtain ⟨b,Lx2⟩:=l01 x2 (m0 S2)
   have T1:qo 0 b (-y2) 0∈L:=by simpa using qh Lx2 S2 1 (-1)
   have b0:b≠0:=λ e=>x20 (nx (by rw[e] at Lx2;exact Lx2))
   have c8a:∀ i,x2 i≠0-> ∀ y∈qH L 1,y i=0:=λ i hi y hy=>by obtain ⟨a,ha⟩:=l10 y hy;have:=dz i S2 ha;simp at this;exact this.resolve_left hi
   have c8b:∀ i,b i≠0-> ∀ u∈qH L 0,u i=0:=λ i hi u hu=>by obtain ⟨b',hb'⟩:=l01 u hu;have:=dz i hb' T1;simp at this;exact this.resolve_right hi
   have xb:∀ i,x2 i*b i=0:=λ i=>by simpa using dz i S2 T1
   have xv:zr x2 v=0:=by rw[qO];simpa[z8] using (qR hL hv S2).2.1
   have xw:zr x2 w=0:=by rw[qO];simpa[z8,wy2] using (qR hL hw S2).2.1
   have bv:zr b v=0:=by rw[qO];simpa[z8] using (qR hL hv T1).2.1
   have bw:zr b w=0:=by rw[qO];simpa[z8,yY,wy2] using (qR hL hw T1).2.1
   obtain ⟨α,β,hαβ⟩:=Yi v0 w0 sv sw dvw x20 b0 xb xv xw bv bw (tU0 S2) (tU1 T1)
   have hz:∀ i,(∀ u∈qH L 0,u i=0)\/∀ y∈qH L 1,y i=0:=λ i=>by
    by_cases hx:x2 i=0
    . exact Or.inl (c8b i λ hb=>by have:=hαβ i;rw[hx,hb] at this;simp at this)
    . exact Or.inr (c8a i hx)
   obtain ⟨x1,hx1,hx1n⟩:=IsConcreteLE.exists_of_lt (lt_of_le_of_ne ((span_singleton_le_iff_mem _ _).2 (m0 S2)) λ e=>by have:=n 0;rw[← e,finrank_span_singleton x20] at this;omega)
   obtain ⟨b1,Lx1⟩:=l01 x1 hx1
   have U0:=wV (n 0) (m0 S2) hx1 x20 λ κ e=>hx1n (by rw[e];exact smul_mem _ _ (mem_span_singleton_self _))
   have U1:=wV (n 1) (m1 Lx2) (m1 Lx1) b0 λ κ e=>hx1n (by rw[show x1=κ•x2 from sub_eq_zero.1 (nx (by simpa[e,sub_eq_add_neg] using qh Lx1 Lx2 1 (-κ)))];exact smul_mem _ _ (mem_span_singleton_self _))
   have q1:=QQ (mem_sup_left Lx2);have q2:=QQ (mem_sup_left Lx1);have q3:=QQ (mem_sup_left (yC S2 Lx1));have q4:=QQ (mem_sup_left (yC T1 Lx1));simp only[zero_add] at q3 q4
   have Q:∀ u∈qH L 0,∀ y∈qH L 1,qa u y v w=0:=λ u hu y hy=>by
    obtain ⟨a,a',rfl⟩:=U0 u hu;obtain ⟨d,d',rfl⟩:=U1 y hy;simp only[qa,qN] at q1 q2 q3 q4 ⊢;linear_combination a*d*q1+a*d'*(q3-q2)+a'*d*(q4-q2)+a'*d'*q2
   refine J4 (n 0) (n 1) sv sw v0 w0 hz (λ i j k l hD z0i z0j z1k z1l=>?_) Q
   obtain ⟨h1,h2,h3,h4,h5,h6'⟩:=hD
   have xi:=z0i x2 (m0 S2);have xj:=z0j x2 (m0 S2);have bk:=z1k b (m1 Lx2);have bl:=z1l b (m1 Lx2)
   have ak:=hαβ k;have al:=hαβ l;have bi:=hαβ i;have bj:=hαβ j
   rw[bk,mul_zero,add_zero] at ak;rw[bl,mul_zero,add_zero] at al;rw[xi,mul_zero,zero_add] at bi;rw[xj,mul_zero,zero_add] at bj
   obtain ⟨r1,r2⟩:=J8 ⟨h6',h2.symm,h4.symm,h3.symm,h5.symm,h1⟩ xi xj ak al xv xw (tU0 S2)
   obtain ⟨r3,r4⟩:=J8 ⟨h1,h2,h3,h4,h5,h6'⟩ bk bl bi bj bv bw (tU1 T1)
   intro m;rcases kY i j k l m ⟨h1,h2,h3,h4,h5,h6'⟩ with rfl|rfl|rfl|rfl;exacts[r3,r4,r1,r2]
 push Not at hB
 have A1:∀ u∈qH L 0,∃ c d,qo u 0 c d∈L:=λ u hu=>by obtain ⟨a,b,rfl⟩:=wV (n 0) (m0 S2) (m0 S3) x20 hB u hu;exact ⟨_,_,by simpa using qh S2 S3 a b⟩
 have A2:∀ y∈qH L 1,∃ c d,qo 0 y c d∈L:=λ y hy=>by obtain ⟨a,ha⟩:=l10 y hy;obtain ⟨c,d,hcd⟩:=A1 a (m0 ha);exact ⟨_,_,by simpa using qh ha hcd 1 (-1)⟩
 have Qf:∀ u∈qH L 0,∀ y∈qH L 1,qa u y v w=0:=λ u hu y hy=>by obtain ⟨c,d,h1⟩:=A1 u hu;obtain ⟨c',d',h2⟩:=A2 y hy;simpa using QQ (mem_sup_left (yC h1 h2))
 have hz:∀ i,(v i≠0\/w i≠0)-> (∀ u∈qH L 0,u i=0)\/∀ y∈qH L 1,y i=0:=λ i hi=>by
  by_contra hc;push Not at hc;obtain ⟨⟨u,hu,hui⟩,⟨y,hy,hyi⟩⟩:=hc;obtain ⟨c,d,h1⟩:=A1 u hu;obtain ⟨c',d',h2⟩:=A2 y hy;exact mul_ne_zero hui hyi (hCI i hi h1 h2)
 have t0:∀ u∈qH L 0,qp u v w=0:=λ u hu=>by obtain ⟨c,d,h⟩:=A1 u hu;exact tU0 h
 have t1:∀ y∈qH L 1,qp y v w=0:=λ y hy=>by obtain ⟨c,d,h⟩:=A2 y hy;exact tU1 h
 by_cases hn:∀ i,v i*w i=0
 . exact J4 (n 0) (n 1) sv sw v0 w0 (λ i=>hz i (Yh v w hn sv sw v0 w0 i)) (λ _ _ _ _ _ _ _ _ _=>hn) Qf
 push Not at hn
 have hz:∀ i,v i*w i≠0-> (∀ u∈qH L 0,u i=0)\/∀ y∈qH L 1,y i=0:=λ i h=>hz i (Or.inl (left_ne_zero_of_mul h))
 obtain ⟨a,ha⟩:=hn
 obtain ⟨b,hab,hb⟩:∃ b,b≠a/\v b*w b≠0:=by by_contra hc;push Not at hc;simp only[zr] at dvw;rcases kR a with rfl|rfl|rfl|rfl<;>grind
 obtain ⟨c,d,h1,h2,h3,h4,h5,h6'⟩:=xl a b (hab.symm)
 have nc:v c*w c=0:=by_contra λ h=>J5 (n 0) (n 1) hz t0 t1 (l:=d) ⟨h1,h2,h3,h4,h5,h6'⟩ ha hb h
 have nd:v d*w d=0:=by_contra λ h=>J5 (n 0) (n 1) hz t0 t1 (l:=c) ⟨h1,h3,h2,h5,h4,h6'.symm⟩ ha hb h
 have hs:v a*w a+v b*w b=0:=by have:=wT (v*w) ⟨h1,h2,h3,h4,h5,h6'⟩;simp only[zr,qN] at dvw this;linear_combination dvw-this-nc-nd
 have eqab:∀ x:qi,qp x v w=0-> x a=x b:=λ x hx=>by
  have e:=wT (x*(v*w)) ⟨h1,h2,h3,h4,h5,h6'⟩;simp only[qp,qN] at hx e
  exact sub_eq_zero.1 ((mul_eq_zero.1 (by linear_combination hx-e-x c*nc-x d*nd-x b*hs:v a*w a*(x a-x b)=0)).resolve_left ha)
 obtain ⟨u0,hu0,α,rfl⟩:=J7 h1 (n 0) (qg hL 0) λ u hu=>eqab u (t0 u hu)
 obtain ⟨u1,hu1,β,rfl⟩:=J7 h1 (n 1) (qg hL 1) λ u hu=>eqab u (t1 u hu)
 have key:v c*w d+v d*w c=0:=by
  have q:=Qf _ hu0 _ hu1;have ta:=t0 _ hu0;have tb:=t1 _ hu1;have K:=(ZG ⟨h1,h2,h3,h4,h5,h6'⟩ v w).2
  simp only[qa,qp,zL,zr,qN] at q ta tb sv sw dvw K;grind
 have rowU:∀ T∈L,∀ k,k=0\/k=1-> T (k,a)=T (k,b):=λ T hT k hk=>by rcases hk with rfl|rfl;exacts[eqab _ (t0 _ ⟨T,hT,rfl⟩),eqab _ (t1 _ ⟨T,hT,rfl⟩)]
 have fin:∀ {r r':Fin 4} {z:qi},z∈qB L r-> zL z=0-> z c=0-> z d=0-> z a≠0-> (∀ T∈L,zr z (λ j=>T (r',j))= -(zr z (λ j=>T (0,j))+zr z (λ j=>T (1,j))))-> (∀ k,k=0\/k=1\/k=r\/k=r')-> False:=by
  intro r r' z hz sz zc zd za hrel hcov;obtain ⟨ez,dz⟩:=J6 ⟨h1,h2,h3,h4,h5,h6'⟩ sz zc zd;set ζ:=z a
  have hv':yu r (Pi.single a 1-Pi.single b 1)∈L:=by have:yu r (ζ⁻¹•z)∈L:=(by rw[map_smul];exact L.smul_mem _ hz);rwa[ez,smul_smul,inv_mul_cancel₀ za,one_smul] at this
  refine Jg hL h6 (r:=r) h1 hv' λ T hT k hk=>?_
  rcases hcov k with hk'|hk'|hk'|hk'
  . exact rowU T hT k (Or.inl hk')
  . exact rowU T hT k (Or.inr hk')
  . exact absurd hk' hk
  . subst hk';have:=hrel T hT;rw[dz,dz,dz,rowU T hT 0 (Or.inl rfl),rowU T hT 1 (Or.inr rfl),sub_self,sub_self,mul_zero,add_zero,neg_zero] at this;exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left za)
 have pj:=λ {r} {z:qi} (hz:z∈qB L r) (T:ze) (hT:T∈L)=>(qR hL hz (by convert hT using 1;funext ⟨i,j⟩;fin_cases i<;>rfl:qo (λ j=>T (0,j)) (λ j=>T (1,j)) (λ j=>T (2,j)) (λ j=>T (3,j))∈L)).2.1
 rcases Yg key nc nd with ⟨vc,vd⟩|⟨wc,wd⟩
 . exact fin (r:=2) (r':=3) hv sv vc vd (left_ne_zero_of_mul ha) (λ T hT=>by have:=pj hv T hT;simp[z8] at this;linear_combination this) (by decide)
 . exact fin (r:=3) (r':=2) hw sw wc wd (right_ne_zero_of_mul ha) (λ T hT=>by have:=pj hw T hT;simp[z8] at this;linear_combination this) (by decide)
lemma ZR (p0:finrank KD (qB L 0)=0) (p1:finrank KD (qB L 1)=1) (p2:finrank KD (qB L 2)=1) (p3:finrank KD (qB L 3)=1):False:=by
 obtain ⟨v1,hv1,v10⟩:=wR p1;obtain ⟨v2,hv2,v20⟩:=wR p2;obtain ⟨v3,hv3,v30⟩:=wR p3
 have s1:=yz hL hv1;have s2:=yz hL hv2;have s3:=yz hL hv3;have M1:=yK.2.1.1 hv1;have M2:=yK.2.2.1.1 hv2;have M3:=yK.2.2.2.1 hv3
 obtain ⟨z1,q1,z10,Q1⟩:=kZ (L:=L) 0 1 2 3 (by simp[n,p1,h6]);obtain ⟨z2,q2,z20,Q2⟩:=kZ (L:=L) 0 2 1 3 (by simp[n,p2,h6]);obtain ⟨z3,q3,z30,Q3⟩:=kZ (L:=L) 0 3 1 2 (by simp[n,p3,h6]);simp only[jw] at Q1 Q2 Q3
 have J:=λ {i p} (h:yu i p∈L) {a b c d:qi} (T:qo a b c d∈L)=>(qR hL h T).2
 have d12:zr v1 v2=0:=by simpa[z8] using (J hv1 M2).1
 have d13:zr v1 v3=0:=by simpa[z8] using (J hv1 M3).1
 have d23:zr v2 v3=0:=by simpa[z8] using (J hv2 M3).1
 have e1:zr v1 z1=0:=by simpa[z8] using (J hv1 Q1).1
 have e2:zr v2 z2=0:=by simpa[z8] using (J hv2 Q2).1
 have e3:zr v3 z3=0:=by simpa[z8] using (J hv3 Q3).1
 have r12:zr v1 z2+zr v1 q2=0:=by simpa[z8] using (J hv1 Q2).1
 have r13:zr v1 z3+zr v1 q3=0:=by simpa[z8] using (J hv1 Q3).1
 have r21:zr v2 z1+zr v2 q1=0:=by simpa[z8] using (J hv2 Q1).1
 have r23:zr v2 z3+zr v2 q3=0:=by simpa[z8] using (J hv2 Q3).1
 have r31:zr v3 z1+zr v3 q1=0:=by simpa[z8] using (J hv3 Q1).1
 have r32:zr v3 z2+zr v3 q2=0:=by simpa[z8] using (J hv3 Q2).1
 have t:zr (v1*v2) v3=0:=(ZL v1 v2 v3).2.1.trans (kB s1 s3 d13 (by simpa[z8] using (J hv1 (yC M2 M3)).2.1))
 have a12:zr (v1*v2) z1=0:=kB s1 s2 d12 (by simpa[z8] using (J hv1 (yC Q1 M2)).2.1)
 have a21:zr (v2*v1) z2=0:=kB s2 s1 ((qO _ _).trans d12) (by simpa[z8] using (J hv2 (yC Q2 M1)).2.1)
 have a13:zr (v1*v3) z1=0:=kB s1 s3 d13 (by simpa[z8] using (J hv1 (yC Q1 M3)).2.1)
 have a31:zr (v3*v1) z3=0:=kB s3 s1 ((qO _ _).trans d13) (by simpa[z8] using (J hv3 (yC Q3 M1)).2.1)
 have a23:zr (v2*v3) z2=0:=kB s2 s3 d23 (by simpa[z8] using (J hv2 (yC Q2 M3)).2.1)
 have a32:zr (v3*v2) z3=0:=kB s3 s2 ((qO _ _).trans d23) (by simpa[z8] using (J hv3 (yC Q3 M2)).2.1)
 have P4:=λ u=>J9 u v1 v2 v3 s1 s2 s3 d12 d13 d23 t
 have E1:zr (v1*v2*v3) z1=0:=by have h:=(J hv1 (yC (yC Q1 M2) M3)).2.2;have e:=P4 z1;simp[z8] at h;simp only[qa] at h e;linear_combination (e-h)/6
 have E2:zr (v1*v2*v3) z2=0:=by have h:=(J hv2 (yC (yC Q2 M1) M3)).2.2;have e:=P4 z2;simp[z8] at h;simp only[qa] at h e;linear_combination (e-h)/6
 have E3:zr (v1*v2*v3) z3=0:=by have h:=(J hv3 (yC (yC Q3 M1) M2)).2.2;have e:=P4 z3;simp[z8] at h;simp only[qa] at h e;linear_combination (e-h)/6
 have nx:∀ {e:qi},qo e 0 0 0∈L-> e=0:=λ h=>ki p0 (yK.1.2 h)
 have S1:=wV (n 1) (wg hv1) (⟨_,Q1,rfl⟩:q1∈qH L 1) v10 λ κ e=>z10 (nx (by simpa[e] using qh Q1 M1 1 (-κ)))
 have S2:=wV (n 2) (wg hv2) (⟨_,Q2,rfl⟩:q2∈qH L 2) v20 λ κ e=>z20 (nx (by simpa[e] using qh Q2 M2 1 (-κ)))
 have S3:=wV (n 3) (wg hv3) (⟨_,Q3,rfl⟩:q3∈qH L 3) v30 λ κ e=>z30 (nx (by simpa[e] using qh Q3 M3 1 (-κ)))
 have hsp:=Ja p0 S1 S2 S3 M1 M2 M3 Q1 Q2 Q3
 have Zp:∀ x,zr x z1=0-> zr x z2=0-> zr x z3=0-> ∀ u∈qH L 0,zr x u=0:=λ x h1 h2 h3 u hu=>by obtain ⟨a,b,c,rfl⟩:=hsp u hu;simp[yY,h1,h2,h3]
 have hk:∀ {v x q z:qi} {k:Fin 4},(∀ u∈qH L k,∃ a b:KD,u=a•x+b•q)-> zr v x=0-> zr v z+zr v q=0-> zr v z=0-> ∀ u∈qH L k,zr v u=0:=λ {v x q z k} S dx r f u hu=>by obtain ⟨a,b,rfl⟩:=S u hu;have hq:zr v q=0:=(by linear_combination r-f);simp[yY,dx,hq]
 refine ZM (n 0) (qg hL 0) ⟨_,Q1,rfl⟩ ⟨_,Q2,rfl⟩ ⟨_,Q3,rfl⟩ z10 z20 z30 Zp (Zp _ E1 E2 E3) s1 s2 s3 v10 v20 v30 d12 d13 d23 t e1 e2 e3 a12 a21 a13 a31 a23 a32 ?_ ?_ ?_<;>intro F x y hxy hm
 . refine ZQ hL h6 hv1 v10 s1 (λ k hk' u hu=>?_) hxy hm;rcases kR k with rfl|rfl|rfl|rfl;exacts[F u hu,absurd rfl hk',hk S2 d12 r12 (F z2 ⟨_,Q2,rfl⟩) u hu,hk S3 d13 r13 (F z3 ⟨_,Q3,rfl⟩) u hu]
 . refine ZQ hL h6 hv2 v20 s2 (λ k hk' u hu=>?_) hxy hm;rcases kR k with rfl|rfl|rfl|rfl;exacts[F u hu,hk S1 ((qO _ _).trans d12) r21 (F z1 ⟨_,Q1,rfl⟩) u hu,absurd rfl hk',hk S3 d23 r23 (F z3 ⟨_,Q3,rfl⟩) u hu]
 . refine ZQ hL h6 hv3 v30 s3 (λ k hk' u hu=>?_) hxy hm;rcases kR k with rfl|rfl|rfl|rfl;exacts[F u hu,hk S1 ((qO _ _).trans d13) r31 (F z1 ⟨_,Q1,rfl⟩) u hu,hk S2 ((qO _ _).trans d23) r32 (F z2 ⟨_,Q2,rfl⟩) u hu,absurd rfl hk']
end
lemma YA (hr:∀ i,finrank KD (L.map (z9 i))≤2):False:=by
 have hPU:∀ i,finrank KD (qB L i)≤2:=λ i=>(finrank_mono wg).trans (hr i)
 obtain ⟨σ,s1,s2,s3⟩:=(by decide:∀ f:Fin 4-> Fin 3,∃ σ:Equiv.Perm (Fin 4),f (σ 0)≤f (σ 1)/\f (σ 1)≤f (σ 2)/\f (σ 2)≤f (σ 3)) λ i=>⟨finrank KD (qB L i),by have:=hPU i;omega⟩
 simp only[Fin.mk_le_mk] at s1 s2 s3
 have hL':=zH hL σ 1;have h6':=(zF L σ 1).trans h6
 have eU:∀ i,finrank KD (qH (L.map (zq σ 1:ze →ₗ[KD] ze)) i)=finrank KD (qH L (σ i)):=λ i=>by rw[(Jb σ i).1]
 have eP:∀ i,finrank KD (qB (L.map (zq σ 1:ze →ₗ[KD] ze)) i)=finrank KD (qB L (σ i)):=λ i=>by rw[(Jb σ i).2]
 generalize L.map (zq σ 1:ze →ₗ[KD] ze)=L' at hL' h6' eU eP
 have nU:∀ i,finrank KD (qH L' i)≤2:=λ i=>(eU i).trans_le (hr _)
 have PU:∀ i,finrank KD (qB L' i)≤finrank KD (qH L' i):=λ i=>finrank_mono wg
 have d0:=xe (L:=L') 1 0 2 3;have d1:=xe (L:=L') 0 1 2 3;have d2:=xe (L:=L') 0 2 1 3;have d3:=xe (L:=L') 0 3 1 2
 rw[← eP 0,← eP 1] at s1;rw[← eP 1,← eP 2] at s2;rw[← eP 2,← eP 3] at s3
 have nb:∀ i,finrank KD (qB L' i)≠0-> qB L' i≠⊥:=λ i h e=>h (by rw[e,finrank_bot])
 have n0:=nU 0;have n1:=nU 1;have n2:=nU 2;have n3:=nU 3;have q0:=PU 0;have q1:=PU 1;have q2:=PU 2;have q3:=PU 3
 by_cases a0:finrank KD (qB L' 0) ≥ 1
 . exact Yp hL' λ i=>nb i (by rcases kR i with rfl|rfl|rfl|rfl<;>omega)
 by_cases a1:finrank KD (qB L' 2)=2
 . exact Jc hL' a1 (by omega)
 by_cases a2:finrank KD (qB L' 3)=2/\finrank KD (qB L' 1) ≥ 1
 . exact Jd hL' a2.1 (nb 1 (by omega)) (nb 2 (by omega))
 by_cases a3:finrank KD (qH L' 0)≤1
 . exact Yw hL' h6' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
 have nn:∀ i,finrank KD (qH L' i)=2:=λ i=>by rcases kR i with rfl|rfl|rfl|rfl<;>omega
 have p0:finrank KD (qB L' 0)=0:=by omega
 rcases (by omega:finrank KD (qB L' 3)=0\/finrank KD (qB L' 3)=1\/finrank KD (qB L' 3)=2) with c3|c3|c3
 . exact Yx hL' h6' nn λ i=>by rcases kR i with rfl|rfl|rfl|rfl<;>omega
 . rcases (by omega:finrank KD (qB L' 2)=0\/finrank KD (qB L' 2)=1) with c2|c2
   . exact Yz hL' h6' nn p0 (by omega) c2 c3
   rcases (by omega:finrank KD (qB L' 1)=0\/finrank KD (qB L' 1)=1) with c1|c1
   . exact Jj hL' h6' nn p0 c1 c2 c3
   . exact ZR hL' h6' nn p0 c1 c2 c3
 rcases (by omega:finrank KD (qB L' 2)=0\/finrank KD (qB L' 2)=1) with c2|c2
 . exact Yy hL' h6' nn p0 (by omega) c2 c3
 . exact Ji hL' h6' nn p0 (by omega) c2 c3
end
end
theorem yL : ∀ L : Submodule KD ze, zg L -> Module.finrank KD L = 6 ->
    (∃ i, Module.finrank KD (L.map (z9 i)) = 3) /\ ∃ j, Module.finrank KD (L.map (zD j)) = 3 := by
 have R:∀ L:Submodule KD ze,zg L-> finrank KD L=6-> ∃ i,finrank KD (L.map (z9 i))=3:=λ L hL h6=>by by_contra h;push Not at h;exact YA hL h6 λ i=>by have:=yq hL i;have:=h i;omega
 intro L hL h6;refine ⟨R L hL h6,?_⟩
 obtain ⟨j,hj⟩:=R _ (zX hL) ((zT L).trans h6)
 exact ⟨j,by rw[← map_comp] at hj;exact hj⟩
end
section
open Module Fin
open Fintype (sum_prod_type)
open Pi (single)
open LinearMap (ker mem_ker proj pi)
open Submodule (span mem_map_of_mem mem_sup mem_span_singleton eq_of_le_of_finrank_le mem_top mem_span_range_iff_exists_fun finrank_sup_add_finrank_inf_eq subset_span eq_top_of_finrank_eq)
variable {L : Submodule KD ze} (J : zg L) (O : finrank KD L = 6) (I : y7 ∈ L) {z : Fin 3 -> KD}
noncomputable def kS : ze →ₗ[KD] ze →ₗ[KD] KD := by
  refine LinearMap.mk₂ KD (fun X Y => ((∑ p, X p) * (∑ p, Y p) - ∑ i, (∑ j, X (i, j)) * (∑ j, Y (i, j)) - ∑ j, (∑ i, X (i, j)) * (∑ i, Y (i, j)) + ∑ p, X p * Y p) / 2) ?_ ?_ ?_ ?_ <;> intros <;> simp [sum_prod_type, sum_univ_four] <;> ring
theorem Jk (X Y) : kS X Y = kS Y X := by simp [kS, sum_prod_type, sum_univ_four]; ring
def kt (z : Fin 14 -> KD) : ze := fun p => let s := z 5 + z 6 + z 7; (![![-z 3 - z 0 - z 1 - z 2 + 3 * s + z 13, z 5 + z 8, z 6 + z 9, z 7 + z 10], ![z 3 - 5 * s + z 4, z 0 - z 5 + z 6 + z 7 + z 11, z 1 + z 5 - z 6 + z 7 + z 12, z 2 + z 5 + z 6 - z 7 - z 11 - z 12], ![z 3 - 5 * s - z 4, z 0 - z 5 + z 6 + z 7 - z 11, z 1 + z 5 - z 6 + z 7 - z 12, z 2 + z 5 + z 6 - z 7 + z 11 + z 12], ![-z 3 - z 0 - z 1 - z 2 + 3 * s - z 13, z 5 - z 8, z 6 - z 9, z 7 - z 10]] : Fin 4 -> Fin 4 -> KD) p.1 p.2
def jx : (Fin 14 -> KD) →ₗ[KD] ze where
  toFun := kt
  map_add' _ _ := by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [kt] <;> ring
  map_smul' _ _ := by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [kt] <;> ring
def jr (z y : Fin 14 -> KD) : KD := -(z 0 * y 0 + z 1 * y 1 + z 2 * y 2) - 3 * (z 0 + z 1 + z 2) * (y 0 + y 1 + y 2) - z 3 * (y 0 + y 1 + y 2) - y 3 * (z 0 + z 1 + z 2) + 3 * (z 5 * y 5 + z 6 * y 6 + z 7 * y 7) - 9 * (z 5 + z 6 + z 7) * (y 5 + y 6 + y 7) + (z 11 * y 11 + z 12 * y 12 + (z 11 + z 12) * (y 11 + y 12)) + (z 8 * y 8 + z 9 * y 9 + z 10 * y 10) - (z 8 + z 9 + z 10) * (y 8 + y 9 + y 10) - z 13 * (y 8 + y 9 + y 10) - y 13 * (z 8 + z 9 + z 10)
theorem yk (z y) : kS (jx z) (jx y) = jr z y := by simp [kS, jx, kt, jr, sum_prod_type, sum_univ_four]; ring
noncomputable def yA (T : ze) : Fin 14 -> KD := let s := T (0, 1) + T (3, 1) + T (0, 2) + T (3, 2) + T (0, 3) + T (3, 3); ![(T (1, 1) + T (2, 1)) / 2 + (T (0, 1) + T (3, 1)) - s / 2, (T (1, 2) + T (2, 2)) / 2 + (T (0, 2) + T (3, 2)) - s / 2, (T (1, 3) + T (2, 3)) / 2 + (T (0, 3) + T (3, 3)) - s / 2, (T (1, 0) + T (2, 0)) / 2 + 5 * s / 2, (T (1, 0) - T (2, 0)) / 2, (T (0, 1) + T (3, 1)) / 2, (T (0, 2) + T (3, 2)) / 2, (T (0, 3) + T (3, 3)) / 2, (T (0, 1) - T (3, 1)) / 2, (T (0, 2) - T (3, 2)) / 2, (T (0, 3) - T (3, 3)) / 2, (T (1, 1) - T (2, 1)) / 2, (T (1, 2) - T (2, 2)) / 2, (T (0, 0) - T (3, 0)) / 2]
theorem Kl {U : Submodule KD ze} (hU : ∀ T ∈ U, yl T = 0) {n} (χ : (Fin n -> KD) →ₗ[KD] ze) : ∀ x ∈ U.comap χ, ∀ y ∈ U.comap χ, kS.compl₁₂ χ χ x y = 0 :=
  yr (kS.compl₁₂ χ χ) (fun _ _ => Jk _ _) _ fun x G => by have := hU (χ x) G; simp [kS, yl, sum_prod_type, sum_univ_four] at this ⊢; linear_combination this
theorem yU {U : Submodule KD ze} (hU : ∀ T ∈ U, yl T = 0) {n d} (χ : (Fin n -> KD) →ₗ[KD] ze) (P : ∀ T ∈ U, ∃ x, χ x = T) (r : Fin d -> Fin n -> KD) (s : Fin d -> Fin n) (Q : ∀ x, (∀ i, kS (χ x) (χ (single i 1)) = 0) -> x = ∑ k, x (s k) • r k) : 2 * finrank KD U ≤ n + d /\ ((∀ i y, kS (χ (r i)) (χ y) = 0) -> n + d ≤ 2 * finrank KD U + 1 -> ∀ i, χ (r i) ∈ U) := by
  have h1 := Submodule.finrank_map_le χ (U.comap χ)
  rw [show (U.comap χ).map χ = U from le_antisymm (Submodule.map_comap_le _ _) fun T H => by obtain ⟨x, rfl⟩ := P T H; exact ⟨x, H, rfl⟩] at h1
  set B := kS.compl₁₂ χ χ
  set U' := U.comap χ
  set R := span KD (Set.range r)
  have hkR : ker B ≤ R := fun x G => (mem_span_range_iff_exists_fun KD).2 ⟨_, (Q x fun i => LinearMap.congr_fun (mem_ker.1 G) _).symm⟩
  have hRd : finrank KD R ≤ d := (finrank_range_le_card r).trans (by simp)
  refine ⟨by have h2 := qr B U' U' (Kl hU χ); have := Submodule.finrank_mono (inf_le_right.trans hkR : U' ⊓ ker B ≤ _); rw [finrank_fin_fun] at h2; omega, fun hr0 hnd => ?_⟩
  have hRk : R ≤ ker B := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact mem_ker.2 (LinearMap.ext (hr0 i)))
  have h2 := qr B U' (U' ⊔ R) fun x G y hy => by
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := mem_sup.1 hy
    rw [map_add, Kl hU χ x G y1 hy1, zero_add]
    exact (Jk _ _).trans (LinearMap.congr_fun (mem_ker.1 (hRk hy2)) x)
  have h3 := finrank_sup_add_finrank_inf_eq U' R
  rw [le_antisymm (inf_le_inf_left _ hkR) (inf_le_inf_left _ hRk), finrank_fin_fun] at h2
  have hRle : R ≤ U' := (eq_of_le_of_finrank_le (inf_le_right : U' ⊓ R ≤ R) (by omega)) ▸ inf_le_left
  exact fun i => hRle (subset_span ⟨i, rfl⟩)
theorem yD (p q X i j) : zq p q X (i, j) = X (p i, q j) := rfl
def qt (p : Fin 4 × Fin 4) : ze →ₗ[KD] KD := proj p
def wh : ze →ₗ[KD] Fin 3 -> KD := pi fun k => qt (1, k.succ) - qt (2, k.succ)
def Wk (L : Submodule KD ze) : Prop := ∀ x : Fin 3 -> KD, x 0 + x 1 + x 2 = 0 -> ∃ T ∈ L, T (1, 1) - T (2, 1) = x 0 /\ T (1, 2) - T (2, 2) = x 1 /\ T (1, 3) - T (2, 3) = x 2
abbrev zS {n} (k : Fin n) : (Fin n -> KD) →ₗ[KD] KD := proj k
theorem Ql {T : ze} : T ∈ L ⊓ ker wh ↔ T ∈ L /\ T (1, 1) = T (2, 1) /\ T (1, 2) = T (2, 2) /\ T (1, 3) = T (2, 3) := by simp [funext_iff, forall_fin_succ, wh, qt, sub_eq_zero]
theorem YB (S : Wk L) (L1 L2 : ze →ₗ[KD] KD) (h : ∀ T ∈ L, (T (1, 1) - T (2, 1)) * L2 T + (T (1, 2) - T (2, 2)) * L1 T = 0) : ∃ κ : KD, ∀ T ∈ L, L2 T = κ * (T (1, 2) - T (2, 2)) /\ L1 T = -κ * (T (1, 1) - T (2, 1)) := by
  obtain ⟨T1, h1, a1, a2, -⟩ := S ![1, 0, -1] (by simp)
  obtain ⟨T2, h2, b1, b2, -⟩ := S ![0, 1, -1] (by simp)
  simp at a1 a2 b1 b2
  exact yF L (qt (1, 1) - qt (2, 1)) (qt (1, 2) - qt (2, 2)) L1 L2 h1 h2 (by simp [qt, a1]) (by simp [qt, a2]) (by simp [qt, b1]) (by simp [qt, b2]) h
def vM : ze := fun p => if p = (0, 0) then 1 else if p = (3, 0) then -1 else 0
def Jl : ze := fun p => if p = (0, 0) \/ p = (3, 0) then 1 else if p = (1, 0) \/ p = (2, 0) then -1 else 0
def x4 : ze →ₗ[KD] Fin 3 -> KD := pi fun k => qt (1, k.succ) + qt (2, k.succ)
def wk (v : Fin 4 -> Fin 4) (h : ∀ i, v (v i) = i) : Equiv.Perm (Fin 4) := ⟨v, v, h, h⟩
def v6 (κ κ' : KD) : (Fin 10 -> KD) →ₗ[KD] Fin 14 -> KD := pi ![zS 0, zS 1, zS 2, zS 3, zS 4, zS 5 + κ • zS 8, zS 5 - κ • zS 7, zS 5, zS 6 + κ' • zS 8, zS 6 - κ' • zS 7, zS 6, zS 7, zS 8, zS 9]
def jY (κ κ' : KD) : (Fin 10 -> KD) →ₗ[KD] Fin 14 -> KD := pi ![zS 0, zS 1, zS 2, zS 3, zS 4, zS 5 + κ • zS 8, zS 5 - κ • zS 7, zS 5, zS 6, (-κ') • zS 8, (-κ') • zS 7 + (-κ') • zS 8, zS 7, zS 8, zS 9]
def xn (L : Submodule KD ze) (z : Fin 3 -> KD) : Prop := ∀ T ∈ L, z 0 * (T (0, 1) + T (3, 1)) + z 1 * (T (0, 2) + T (3, 2)) + z 2 * (T (0, 3) + T (3, 3)) = 0 /\ T (0, 1) * (z 1 * T (3, 3) + z 2 * T (3, 2)) + T (0, 2) * (z 0 * T (3, 3) + z 2 * T (3, 1)) + T (0, 3) * (z 0 * T (3, 2) + z 1 * T (3, 1)) = 0
def ZS (L : Submodule KD ze) (z : Fin 3 -> KD) : Prop := ∀ T ∈ L, ∃ t : KD, T (2, 1) = T (1, 1) - t * z 0 /\ T (2, 2) = T (1, 2) - t * z 1 /\ T (2, 3) = T (1, 3) - t * z 2
def kC (L : Submodule KD ze) : Prop := ∀ T ∈ L, T (0, 1) - T (3, 1) + (T (0, 2) - T (3, 2)) + (T (0, 3) - T (3, 3)) = 0
def Jm (L : Submodule KD ze) (z : Fin 3 -> KD) : Prop := z ∈ L.map wh /\ ∀ x ∈ L.map wh, ∃ c : KD, x = c • z
theorem ZT (C : Jm L z) : ZS L z := fun T H => by
  obtain ⟨t, h⟩ := C.2 _ (mem_map_of_mem H)
  simp [funext_iff, forall_fin_succ, wh, qt] at h; exact ⟨t, by grind⟩
def jE (z p q : Fin 3 -> KD) : KD := p 0 * (z 1 * q 2 + z 2 * q 1) + p 1 * (z 0 * q 2 + z 2 * q 0) + p 2 * (z 0 * q 1 + z 1 * q 0)
noncomputable def xo (z : Fin 3 -> KD) : (Fin 6 -> KD) →ₗ[KD] (Fin 6 -> KD) →ₗ[KD] KD := by
  refine LinearMap.mk₂ KD (fun x y => (jE z ![x 0, x 1, x 2] ![y 3, y 4, y 5] + jE z ![y 0, y 1, y 2] ![x 3, x 4, x 5]) / 2) ?_ ?_ ?_ ?_ <;> intros <;> simp [jE] <;> ring
def kj : ze →ₗ[KD] Fin 6 -> KD := pi ![qt (0, 1), qt (0, 2), qt (0, 3), qt (3, 1), qt (3, 2), qt (3, 3)]
theorem YC {V : Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (Y : Submodule KD V) {o : V} (ho : o ∉ Y) : finrank KD (Y ⊔ span KD {o} : Submodule KD V) = finrank KD Y + 1 := by
  have h0 : o ≠ 0 := fun h => ho (h ▸ Y.zero_mem)
  have := finrank_sup_add_finrank_inf_eq Y (span KD {o})
  rw [disjoint_iff.1 ((Submodule.disjoint_span_singleton' h0).2 ho), finrank_bot, finrank_span_singleton h0] at this; omega
theorem vN {V : Type} [AddCommGroup V] [Module KD V] [FiniteDimensional KD V] (N : Submodule KD V) (h : finrank KD N ≤ 1) : ∃ y ∈ N, ∀ x ∈ N, ∃ c : KD, x = c • y := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h
  exact ⟨v, v.2, fun x G => by obtain ⟨c, hc⟩ := hv ⟨x, G⟩; exact ⟨c, congrArg Subtype.val hc.symm⟩⟩
def vO (y : Fin 3 -> KD) : ze := fun p => (![![0, 0, 0, 0], ![0, y 0, y 1, y 2], ![0, -y 0, -y 1, -y 2], ![0, 0, 0, 0]] : Fin 4 -> Fin 4 -> KD) p.1 p.2
noncomputable def jt (z : Fin 3 -> KD) (ya yb : Fin 6 -> KD) : (Fin 9 -> KD) →ₗ[KD] Fin 14 -> KD := pi ![zS 0, zS 1, zS 2, zS 3, zS 4, ((ya 0 + ya 3) / 2) • zS 7 + ((yb 0 + yb 3) / 2) • zS 8, ((ya 1 + ya 4) / 2) • zS 7 + ((yb 1 + yb 4) / 2) • zS 8, ((ya 2 + ya 5) / 2) • zS 7 + ((yb 2 + yb 5) / 2) • zS 8, ((ya 0 - ya 3) / 2) • zS 7 + ((yb 0 - yb 3) / 2) • zS 8, ((ya 1 - ya 4) / 2) • zS 7 + ((yb 1 - yb 4) / 2) • zS 8, ((ya 2 - ya 5) / 2) • zS 7 + ((yb 2 - yb 5) / 2) • zS 8, (z 0 / 2) • zS 5, (z 1 / 2) • zS 5, zS 6]
noncomputable def wl (z : Fin 3 -> KD) (yb : Fin 6 -> KD) : (Fin 8 -> KD) →ₗ[KD] Fin 14 -> KD := pi ![zS 0, zS 1, zS 2, zS 3, zS 4, ((yb 0 + yb 3) / 2) • zS 7, ((yb 1 + yb 4) / 2) • zS 7, ((yb 2 + yb 5) / 2) • zS 7, ((yb 0 - yb 3) / 2) • zS 7, ((yb 1 - yb 4) / 2) • zS 7, ((yb 2 - yb 5) / 2) • zS 7, (z 0 / 2) • zS 5, (z 1 / 2) • zS 5, zS 6]
def kl : ze →ₗ[KD] Fin 3 -> KD := pi ![qt (0, 1) - qt (3, 1), qt (0, 2) - qt (3, 2), qt (0, 3) - qt (3, 3)]
noncomputable def v7 (z : Fin 3 -> KD) : (Fin 3 -> KD) →ₗ[KD] (Fin 3 -> KD) →ₗ[KD] KD := by
  refine LinearMap.mk₂ KD (jE z) ?_ ?_ ?_ ?_ <;> intros <;> simp [jE] <;> ring
noncomputable def vP (z : Fin 3 -> KD) : (Fin 10 -> KD) →ₗ[KD] Fin 14 -> KD := pi ![zS 0, zS 1, zS 2, zS 3, zS 4, zS 7 + (z 0 / 2) • zS 8, zS 7 + (z 1 / 2) • zS 8, zS 7 + (z 2 / 2) • zS 8, (z 0 / 2) • zS 8 + z 0 • zS 9, (z 1 / 2) • zS 8 + z 2 • zS 9, (z 2 / 2) • zS 8 + z 1 • zS 9, (z 0 / 2) • zS 5, (z 1 / 2) • zS 5, zS 6]
noncomputable def km (z : Fin 3 -> KD) (n0 : KD) : (Fin 7 -> KD) →ₗ[KD] Fin 14 -> KD := pi ![zS 0 + z 0 • zS 1, zS 0 + z 1 • zS 1, zS 0 + z 2 • zS 1, zS 2, zS 3, 0, 0, 0, (n0 / 2) • zS 6, (n0 * z 2 / 2) • zS 6, (n0 * z 1 / 2) • zS 6, (z 0 / 2) • zS 4, (z 1 / 2) • zS 4, zS 5]
theorem YD {E : Type} [AddCommGroup E] [Module KD E] (N : Submodule KD E) (f g h : E →ₗ[KD] KD) (hfgh : ∀ x ∈ N, f x * (g x * h x) = 0) {x0 : E} (hx0 : x0 ∈ N) (hf : f x0 ≠ 0) : (∀ x ∈ N, g x = 0) \/ ∀ x ∈ N, h x = 0 := by
  set y := (f x0)⁻¹ • x0
  have hfy : f y = 1 := by simp [y, hf]
  refine zz N g h fun x G => ?_
  have e : ∀ k : KD, k ≠ 0 -> g (x + (k - f x) • y) * h (x + (k - f x) • y) = 0 := fun k hk => by
    have := hfgh (x + (k - f x) • y) (N.add_mem G (N.smul_mem (k - f x) (N.smul_mem _ hx0 : y ∈ N)))
    rw [map_add, map_smul, hfy, smul_eq_mul, mul_one, add_sub_cancel] at this
    exact (mul_eq_zero.1 this).resolve_left hk
  have e1 := e 1 one_ne_zero; have e2 := e 2 two_ne_zero; have e3 := e 3 three_ne_zero
  simp only [map_add, map_smul, smul_eq_mul] at e1 e2 e3
  linear_combination ((f x - 2) * (f x - 3) / 2) * e1 - ((f x - 1) * (f x - 3)) * e2 + ((f x - 1) * (f x - 2) / 2) * e3
abbrev Qm (L : Submodule KD ze) (p : Equiv.Perm (Fin 4)) (r0 : Fin 4) : Submodule KD ze := (L.map (zM : ze →ₗ[KD] ze)).map (zq p (Equiv.swap 0 r0) : ze →ₗ[KD] ze)
def Zc (a0 a1 : KD) : (Fin 10 -> KD) →ₗ[KD] ze := pi fun q => (![![zS 0 + zS 1, zS 2 + zS 3, zS 2 - zS 3, zS 0 - zS 1], ![zS 0 + zS 4, zS 5 - zS 3, zS 5 + zS 3, zS 0 - zS 4], ![a0 • zS 6, a1 • zS 6, a1 • zS 6, a0 • zS 6], ![zS 7, zS 8 + zS 9, zS 8 - zS 9, (-4 : KD) • zS 0 - (2 : KD) • zS 2 - (2 : KD) • zS 5 - (2 * a0 + 2 * a1) • zS 6 - zS 7 - (2 : KD) • zS 8]] : Fin 4 -> Fin 4 -> (Fin 10 -> KD) →ₗ[KD] KD) q.1 q.2
theorem YE : ∀ r i : Fin 4, r ≠ 0 -> i ≠ 0 -> i ≠ r -> ∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 /\ σ 2 = i /\ σ 3 = r := by
  intro r i Q hi hir; refine ⟨Equiv.swap 3 r * Equiv.swap 2 (Equiv.swap 3 r i), ?_⟩; fin_cases r <;> fin_cases i <;> simp at Q hi hir ⊢ <;> decide
section
include J
theorem Zd {T : ze} (H : T ∈ L) (i i' : Fin 4) {l : KD} (h : T (i, 1) = l /\ T (i, 2) = l /\ T (i, 3) = l /\ T (i', 1) = l /\ T (i', 2) = l /\ T (i', 3) = l) (hi : i ≠ i' := by decide) : l = 0 := by
  have e := qP J H (-l); rw [zY] at e
  obtain ⟨a1, a2, a3, b1, b2, b3⟩ := h
  have : (24 : KD) * (-l) ^ 4 = 0 := by rw [← e]; fin_cases i <;> fin_cases i' <;> simp at hi a1 a2 a3 b1 b2 b3 <;> simp [zs, a1, a2, a3, b1, b2, b3]
  simpa using this
theorem wz : ∀ T ∈ L, yl T = 0 := fun _ h => (qb J h).2.1
theorem v8 {T : ze} (h : T ∈ L) : jh T = 0 := (qb J h).2.2.1
theorem Kz (D : ∀ k, z k ≠ 0) (hz3 : z 0 + z 1 + z 2 = 0) (hzs : xn L z) : finrank KD (L.map kj) ≤ 2 /\ ((kC L) -> z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≠ 0 -> finrank KD (L.map kj) ≤ 1) := by
  set Y := L.map kj
  set o : Fin 6 -> KD := fun _ => 1
  have hk : ∀ W : Submodule KD (Fin 6 -> KD), W ⊓ ker (xo z) = ⊥ := fun W => by
    rw [Submodule.eq_bot_iff]; intro x G
    have E : ∀ i, xo z x (single i 1) = 0 := fun i => LinearMap.congr_fun (mem_ker.1 G.2) _
    simp [forall_fin_succ, xo, jE] at E
    have := D 0; have := D 1; have := D 2
    funext i; fin_cases i <;> simp <;> grind
  have hs : ∀ x y, xo z x y = xo z y x := fun x y => by simp [xo, jE]; ring
  have hU := yr _ hs (Y ⊔ span KD {o}) fun x G => by
    obtain ⟨y, ⟨T, H, rfl⟩, u, hu, rfl⟩ := mem_sup.1 G
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hu
    simp [xo, jE, kj, qt, o]; grind [hzs T H]
  have hnot : o ∉ Y := fun ⟨T, H, he⟩ => by have := congrFun he; simp [forall_fin_succ, kj, qt, o] at this; exact one_ne_zero (Zd J H 0 3 (by grind))
  have h1 := qr _ _ _ hU
  rw [hk, finrank_bot, finrank_fin_fun, YC Y hnot] at h1
  refine ⟨by omega, fun Q hzz => ?_⟩
  set wb : Fin 6 -> KD := ![-(z 0 ^ 2), -(z 1 ^ 2), -(z 2 ^ 2), z 0 ^ 2, z 1 ^ 2, z 2 ^ 2]
  have hw : wb ∉ Y ⊔ span KD {o} := fun h => by
    obtain ⟨y, ⟨T, H, rfl⟩, u, hu, e⟩ := mem_sup.1 h
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hu
    have := congrFun e; simp [forall_fin_succ, kj, qt, o, wb] at this; grind [Q T H]
  have hW : ∀ x ∈ Y ⊔ span KD {o}, ∀ x' ∈ (Y ⊔ span KD {o}) ⊔ span KD {wb}, xo z x x' = 0 := by
    intro x G x' G'
    obtain ⟨y', hy', u', hu', rfl⟩ := mem_sup.1 G'
    obtain ⟨c', rfl⟩ := mem_span_singleton.1 hu'
    rw [map_add, hU x G y' hy', map_smul, zero_add, smul_eq_mul]
    refine mul_eq_zero_of_right _ ?_
    obtain ⟨y, ⟨T, H, rfl⟩, u, hu, rfl⟩ := mem_sup.1 G
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 hu
    have := Q T H
    simp [xo, jE, kj, qt, wb, o]; grind
  have h2 := qr _ _ _ hW
  rw [hk, finrank_bot, finrank_fin_fun, YC _ hw, YC Y hnot] at h2
  omega
theorem Jn {y : Fin 3 -> KD} (hy3 : y 0 + y 1 + y 2 = 0) (hyy : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 0) (hy1 : y 1 ≠ 0) (hE : vO y ∈ L) {T : ze} (H : T ∈ L) : y 2 * (T (0, 1) + T (3, 1)) + y 1 * (T (0, 2) + T (3, 2)) + y 0 * (T (0, 3) + T (3, 3)) = 0 := by
  have p := v8 J (L.add_mem hE H); have m := v8 J (L.sub_mem hE H); have u := v8 J H
  simp [jh, zs, z8, sum_univ_four, vO] at p m u
  refine (mul_eq_zero.1 (?_ : y 1 * _ = 0)).resolve_left hy1
  linear_combination (-1 / 4) * p + (1 / 4) * m + (1 / 2) * u + (-T (0, 0) * y 0 - T (0, 0) * y 1 - T (0, 2) * y 0 - T (3, 0) * y 0 - T (3, 0) * y 1 - T (3, 2) * y 0) * hy3 + (T (0, 0) + T (0, 2) + T (3, 0) + T (3, 2)) * ((hyy - (y 2 - y 0 - y 1) * hy3) / 2)
theorem YF (D : ∀ k, z k ≠ 0) (hz0 : z 0 = 1) (hz3 : z 0 + z 1 + z 2 = 0) (hzz : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 0) (hzs : xn L z) (hE : vO (fun k => z k / 2) ∈ L) : ∃ n : Fin 3 -> KD, ∃ l : KD, jE z n n = 0 /\ ∀ T ∈ L, ∃ c : KD, T (0, 1) = c * (l + n 0) / 2 /\ T (0, 2) = c * (l + n 1) / 2 /\ T (0, 3) = c * (l + n 2) / 2 /\ T (3, 1) = c * (l - n 0) / 2 /\ T (3, 2) = c * (l - n 1) / 2 /\ T (3, 3) = c * (l - n 2) / 2 := by
  have hs : ∀ T ∈ L, T (0, 1) + T (3, 1) = T (0, 3) + T (3, 3) /\ T (0, 2) + T (3, 2) = T (0, 3) + T (3, 3) /\ jE z (kl T) (kl T) = 0 := fun T H => by
    have hy := Jn J (y := fun k => z k / 2) (by grind) (by grind) (by simpa using D 1) hE H
    have := hzs T H; have := D 1; have : z 0 - z 2 ≠ 0 := fun h => by grind
    simp [jE, kl, qt]; grind
  have hR := yr (v7 z) (fun x y => by simp [v7, jE]; ring) (L.map kl) fun x ⟨T, H, e⟩ => by rw [← e]; simpa [v7] using (hs T H).2.2
  have hk : ker (v7 z) = ⊥ := by
    rw [Submodule.eq_bot_iff]; intro x G
    have E : ∀ i, v7 z x (single i 1) = 0 := fun i => LinearMap.congr_fun (mem_ker.1 G) _
    simp [forall_fin_succ, v7, jE] at E
    have := D 0; have := D 1; have := D 2
    funext i; fin_cases i <;> simp <;> grind
  have h1 := qr _ _ _ hR
  rw [hk, inf_bot_eq, finrank_bot, finrank_fin_fun] at h1
  obtain ⟨n, ⟨Tn, hTn, rfl⟩, hspan⟩ := vN (L.map kl) (by omega)
  refine ⟨kl Tn, Tn (0, 3) + Tn (3, 3), (hs Tn hTn).2.2, fun T H => ?_⟩
  obtain ⟨c, hc⟩ := hspan _ (mem_map_of_mem H)
  obtain ⟨a1, a2, -⟩ := hs _ (L.sub_mem H (L.smul_mem c hTn)); obtain ⟨b1, b2, -⟩ := hs Tn hTn
  have e := congrFun hc; simp [forall_fin_succ, kl, qt] at e a1 a2
  clear hs hR hspan hk hzs
  have := Zd J (L.sub_mem H (L.smul_mem c hTn)) 0 3 (l := (T (0, 3) - c * Tn (0, 3) + (T (3, 3) - c * Tn (3, 3))) / 2) (by simp; grind)
  exact ⟨c, by simp [kl, qt]; grind⟩
theorem Km (hr0 : finrank KD (L.map (z9 0)) = 3) {a b : Fin 4} (hab : a ≠ b) (h : ∀ T ∈ L, T (0, a) = T (0, b)) : False := by
  let f : (Fin 4 -> KD) →ₗ[KD] KD := (proj a : (Fin 4 -> KD) →ₗ[KD] KD) - proj b
  have hle : L.map (z9 0) ≤ ker f := by rintro _ ⟨T, H, rfl⟩; simp [f, zA, h T H]
  have := Submodule.finrank_lt fun h' : ker f = ⊤ => by simpa [f, hab.symm] using h'.ge (mem_top (x := single a (1 : KD)))
  rw [finrank_fin_fun] at this
  exact qg J 0 (eq_of_le_of_finrank_le hle (by omega) ▸ (by simp [f] : (fun _ => (1 : KD)) ∈ ker f))
end
section
include J I
theorem k6 {T : ze} (H : T ∈ L) :
    T (1, 1) - T (2, 1) + (T (1, 2) - T (2, 2)) + (T (1, 3) - T (2, 3)) = 0 /\ (T (1, 1) - T (2, 1)) * (T (0, 1) + T (3, 1)) + (T (1, 2) - T (2, 2)) * (T (0, 2) + T (3, 2)) + (T (1, 3) - T (2, 3)) * (T (0, 3) + T (3, 3)) = 0 /\
    T (0, 1) * ((T (1, 2) - T (2, 2)) * T (3, 3) + (T (1, 3) - T (2, 3)) * T (3, 2)) + T (0, 2) * ((T (1, 1) - T (2, 1)) * T (3, 3) + (T (1, 3) - T (2, 3)) * T (3, 1)) + T (0, 3) * ((T (1, 1) - T (2, 1)) * T (3, 2) + (T (1, 2) - T (2, 2)) * T (3, 1)) = 0 := by
  obtain ⟨h1, h2, h3⟩ := w8 J I (Submodule.mem_sup_left H)
  simp [yX, zs] at h1 h2 h3
  exact ⟨h1, h2, by linear_combination h3⟩
theorem vQ {T : ze} (H : T ∈ L) {n} {ψ : (Fin n -> KD) →ₗ[KD] Fin 14 -> KD} (x) (h : ψ x = yA T) : ∃ x, (jx ∘ₗ ψ) x = T := ⟨x, by
  have h1 := (qb J H).1; have h2 := (k6 J I H).1
  simp only [qY, sum_prod_type, sum_univ_four] at h1
  rw [LinearMap.comp_apply, h]; funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [jx, kt, yA] <;> grind⟩
theorem YG : finrank KD (L.map wh) ≤ 2 /\ (finrank KD (L.map wh) = 2 -> Wk L) := by
  let f : (Fin 3 -> KD) →ₗ[KD] KD := (proj 0 : (Fin 3 -> KD) →ₗ[KD] KD) + proj 1 + proj 2
  have hle : L.map wh ≤ ker f := by rintro _ ⟨T, H, rfl⟩; simpa [f, wh, qt] using (k6 J I H).1
  have hk : finrank KD (ker f) ≤ 2 := by
    have := Submodule.finrank_lt fun h : ker f = ⊤ => by simpa [f] using h.ge (mem_top (x := single 0 (1 : KD)))
    rw [finrank_fin_fun] at this; omega
  refine ⟨(Submodule.finrank_mono hle).trans hk, fun h2 x G => ?_⟩
  obtain ⟨T, H, e⟩ : x ∈ L.map wh := eq_of_le_of_finrank_le hle (by omega) ▸ (by simpa [f] using G : x ∈ ker f)
  have := congrFun e; simp [forall_fin_succ, wh, qt] at this; exact ⟨T, H, this⟩
theorem ZU (S : Wk L) : ∃ κ : KD, ∀ T ∈ L, T (0, 1) + T (3, 1) - T (0, 3) - T (3, 3) = κ * (T (1, 2) - T (2, 2)) /\ T (0, 2) + T (3, 2) - T (0, 3) - T (3, 3) = -κ * (T (1, 1) - T (2, 1)) :=
  YB S (qt (0, 2) + qt (3, 2) - qt (0, 3) - qt (3, 3)) (qt (0, 1) + qt (3, 1) - qt (0, 3) - qt (3, 3)) fun T H => by simp [qt]; grind [k6 J I H]
theorem Jo (C : Jm L z) : z 0 + z 1 + z 2 = 0 /\ xn L z := by
  obtain ⟨T1, h1, e⟩ := C.1
  simp [funext_iff, forall_fin_succ, wh, qt] at e
  have a1 : T1 (2, 1) = T1 (1, 1) - z 0 := by grind
  have a2 : T1 (2, 2) = T1 (1, 2) - z 1 := by grind
  have a3 : T1 (2, 3) = T1 (1, 3) - z 2 := by grind
  refine ⟨by grind [(k6 J I h1).1], fun T H => ?_⟩
  obtain ⟨t, b1, b2, b3⟩ := ZT C T H
  have g := fun s => k6 J I (L.add_mem H (L.smul_mem s h1))
  have q0 := (k6 J I h1).2.1; have q1 := (g (1 - t)).2.1; have F1 := (g (1 - t)).2.2; have F2 := (g (2 - t)).2.2; have F3 := (g (3 - t)).2.2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, a1, a2, a3, b1, b2, b3] at q0 q1 F1 F2 F3
  exact ⟨by linear_combination q1 - (1 - t) * q0, by linear_combination (3 - 5 / 2 * t + 1 / 2 * t ^ 2) * F1 + (-3 / 2 + 2 * t - 1 / 2 * t ^ 2) * F2 + (1 / 3 - 1 / 2 * t + 1 / 6 * t ^ 2) * F3⟩
theorem YH (hr0 : finrank KD (L.map (z9 0)) = 3) {a b c : Fin 4} (hp : a = 2 /\ b = 3 /\ c = 1 \/ a = 1 /\ b = 3 /\ c = 2 \/ a = 1 /\ b = 2 /\ c = 3) (hdc : ∀ T ∈ L, T (1, c) = T (2, c)) (hdab : ∀ T ∈ L, T (1, a) - T (2, a) = -(T (1, b) - T (2, b))) (hne : ∃ T ∈ L, T (1, a) - T (2, a) ≠ 0) : ∀ T ∈ L, T (0, c) = T (3, c) /\ T (0, a) + T (3, a) = T (0, b) + T (3, b) := by
  obtain ⟨T0, hT0, hne0⟩ := hne
  have hs : ∀ T ∈ L, T (0, a) + T (3, a) = T (0, b) + T (3, b) := by
    rcases zz L (qt (1, a) - qt (2, a)) (qt (0, a) + qt (3, a) - qt (0, b) - qt (3, b)) (fun T H => by have := hdc T H; simp [qt]; grind [k6 J I H, hdab T H]) with h | h
    . exact (hne0 (by simpa [qt] using h T0 hT0)).elim
    . intro T H; have := h T H; simp [qt] at this; grind
  refine fun T H => ⟨?_, hs T H⟩
  rcases YD L (qt (1, a) - qt (2, a)) (qt (0, b) - qt (0, a)) (qt (3, c) - qt (0, c)) (fun T H => by simp [qt]; grind [k6 J I H, hdab T H, hdc T H, hs T H]) hT0 (by simpa [qt] using hne0) with h | h
  . exact (Km J hr0 (a := a) (b := b) (by rcases hp with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> decide) fun T H => by have := h T H; simp [qt] at this; grind).elim
  . have := h T H; simp [qt] at this; grind
end
include J O in
theorem Jp {ya yb : Fin 6 -> KD} (hz3 : z 0 + z 1 + z 2 = 0) (hya : ya 0 + ya 1 + ya 2 - ya 3 - ya 4 - ya 5 = 1) (hyb : yb 0 + yb 1 + yb 2 - yb 3 - yb 4 - yb 5 = 0) (P : ∀ T ∈ L, ∃ x, (jx ∘ₗ jt z ya yb) x = T) : (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≠ 0 -> False) /\ (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 0 -> (jx ∘ₗ jt z ya yb) (single 5 1) ∈ L) := by
  set c := jr (jt z ya yb (single 8 1)) (jt z ya yb (single 7 1)) with hc
  set q := jr (jt z ya yb (single 8 1)) (jt z ya yb (single 8 1)) with hq
  simp [jr, jt] at hc hq
  refine ⟨fun hzz => ?_, fun hzz => ?_⟩
  . have := (yU (wz J) _ P ![single 4 1, single 8 1 + (2 * c) • single 6 1] ![4, 8] fun x G => by simp [forall_fin_succ, yk, jr, jt] at G; funext i; fin_cases i <;> simp [sum_univ_succ] <;> grind).1
    omega
  by_cases hq0 : q = 0
  . exact (yU (wz J) _ P ![single 4 1, single 5 1, single 8 1 + (2 * c) • single 6 1] ![4, 5, 8] (fun x G => by simp [forall_fin_succ, yk, jr, jt] at G; funext i; fin_cases i <;> simp [sum_univ_succ] <;> grind)).2 (fun i y => by
      fin_cases i
      . simp [yk, jr, jt]
      . simp [yk, jr, jt]; linear_combination y 5 / 4 * hzz + y 5 / 4 * (z 0 + z 1 - z 2) * hz3
      . simp [yk, jr, jt]; linear_combination (-y 7) * hc + (-y 7 * c) * hya + y 8 * hq0 - y 8 * hq + (-y 8 * c - y 6 / 2) * hyb) (by omega) 1
  . have := (yU (wz J) _ P ![single 4 1, single 5 1] ![4, 5] fun x G => by simp [forall_fin_succ, yk, jr, jt, funext_iff, sum_univ_succ] at G ⊢; grind).1
    omega
section
include J O I
theorem Kn (hB : vM ∈ L) (hC : Jl ∈ L) : False := by
  have := wL (zX J) 0 fun w hw => ⟨((w 1 - w 2) / 2) • y7 + ((w 0 - w 3) / 2) • vM + ((w 0 + w 3) / 2) • Jl, L.add_mem (L.add_mem (L.smul_mem _ I) (L.smul_mem _ hB)) (L.smul_mem _ hC), by simp only [sum_univ_four] at hw; funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [zQ, y7, vM, Jl] <;> grind⟩
  rw [zT, O] at this; omega
theorem ZV (S : Wk L) (hR : ∀ T ∈ L, (T (0, 2) - T (3, 2)) * (T (1, 3) - T (2, 3)) + (T (0, 3) - T (3, 3)) * (T (1, 2) - T (2, 2)) = 0) : False := by
  obtain ⟨κ, M⟩ := ZU J I S
  obtain ⟨κ', M'⟩ := YB S (qt (0, 3) - qt (3, 3) - (qt (0, 2) - qt (3, 2))) (qt (3, 2) - qt (0, 2)) fun T H => by simp [qt]; grind [hR T H, (k6 J I H).1]
  simp [qt] at M'
  have hkk : κ' ^ 2 = κ ^ 2 := by obtain ⟨T, h3, u⟩ := S ![1, 1, -2] (by norm_num); simp at u; grind [M T h3, M' T h3, (k6 J I h3).2.2]
  have P : ∀ T ∈ L, ∃ x, (jx ∘ₗ jY κ κ') x = T := fun T H => vQ J I H (yA T ∘ ![0, 1, 2, 3, 4, 7, 8, 11, 12, 13]) (by simp [funext_iff, forall_fin_succ, jY, yA]; grind [M T H, M' T H])
  by_cases hD1 : 1 + 4 * κ ^ 2 = 0
  . have := (qb J ((yU (wz J) _ P ![single 4 1, ![0, 0, 0, 0, 0, -κ / 3, 2 * κ', 0, 1, 2 * κ']] ![4, 8] (fun x G => by simp [forall_fin_succ, yk, jr, jY] at G; funext i; fin_cases i <;> simp [sum_univ_succ] <;> grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr, jY]; grind) (by omega) 1)).2.2.2
    simp [k8, zY, zs, jx, kt, jY] at this; grind
  by_cases hD3 : 3 + 4 * κ ^ 2 = 0
  . have hR := (yU (wz J) _ P ![single 4 1, ![0, 0, 0, 0, 0, -κ, 0, -2, 1, 0]] ![4, 8] (fun x G => by simp [forall_fin_succ, yk, jr, jY] at G; funext i; fin_cases i <;> simp [sum_univ_succ] <;> grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr, jY]; grind) (by omega) 1
    have := (yU (wz J) (jx ∘ₗ jY κ κ' ∘ₗ pi ![zS 0, zS 1, zS 2, (-1 : KD) • zS 0 + (-1 / 2 : KD) • zS 1 + (-1 / 2 : KD) • zS 2 + (12 : KD) • zS 4 + (2 / 3 * κ * κ') • zS 5 + (2 / 3 * κ * κ') • zS 8 + (-25 / 6 * κ) • zS 6 + (11 / 3 * κ) • zS 7, zS 3, zS 4, zS 5, zS 6, zS 7, zS 8]) (fun T H => by
        have p := v8 J (L.add_mem hR H); have m := v8 J (L.sub_mem hR H); have u := v8 J H
        simp [jh, zs, z8, sum_univ_four, jx, kt, jY] at p m u
        have hl : 12 * T (0, 0) + 16 * κ * κ' * T (0, 0) - 4 * T (0, 1) + 16 * κ * κ' * T (0, 1) + 8 * T (0, 2) + 8 * T (0, 3) - 12 * T (1, 0) - 12 * T (1, 1) - 8 * κ * T (1, 2) + 8 * κ * T (1, 3) - 12 * T (2, 0) - 12 * T (2, 1) + 8 * κ * T (2, 2) - 8 * κ * T (2, 3) + 12 * T (3, 0) - 16 * κ * κ' * T (3, 0) - 4 * T (3, 1) - 16 * κ * κ' * T (3, 1) + 8 * T (3, 2) + 8 * T (3, 3) = 0 := by grind
        clear p m u; obtain ⟨x, rfl⟩ := P T H
        simp [jx, kt, jY] at hl
        exact ⟨![x 0, x 1, x 2, x 4, x 5, x 6, x 7, x 8, x 9], by simp only [LinearMap.comp_apply]; congr 2; funext i; fin_cases i <;> simp; grind⟩) ![single 3 1, ![0, 0, 0, 0, -κ, 0, -2, 1, 0]] ![3, 7] fun x G => by simp [forall_fin_succ, yk, jr, jY] at G; funext i; fin_cases i <;> simp [sum_univ_succ] <;> grind).1
    omega
  have := (yU (wz J) _ P ![single 4 1] ![4] fun x G => by simp [forall_fin_succ, yk, jr, jY, funext_iff] at G ⊢; grind).1
  omega
set_option maxHeartbeats 2000000 in
theorem YI (h2 : finrank KD (L.map wh) = 2) : False := by
  have S := (YG J I).2 h2
  by_cases hC : ∀ T ∈ L ⊓ ker wh, T (0, 1) = T (3, 1) /\ T (0, 2) = T (3, 2) /\ T (0, 3) = T (3, 3)
  . have S := (YG J I).2 h2
    obtain ⟨κ, M⟩ := ZU J I S
    have hK4 := zW wh L
    set K := L ⊓ ker wh
    have hK0 : ∀ T ∈ K, T (0, 1) = 0 /\ T (0, 2) = 0 /\ T (0, 3) = 0 /\ T (3, 1) = 0 /\ T (3, 2) = 0 /\ T (3, 3) = 0 := fun T H => by
      have := hC T H; obtain ⟨H, e⟩ := Ql.1 H; have := M T H; have := Zd J H 0 3 (l := T (0, 3)) (by grind); grind
    have hB : vM ∈ L := by
      have := (yU (U := K) (fun T H => wz J T H.1) (jx ∘ₗ pi ![zS 0, zS 1, zS 2, zS 3, zS 4, 0, 0, 0, 0, 0, 0, 0, 0, zS 5]) (fun T H => vQ J I H.1 (yA T ∘ ![0, 1, 2, 3, 4, 13]) (by simp [funext_iff, forall_fin_succ, yA]; grind [hK0 T H, Ql.1 H])) ![single 4 1, single 5 1] ![4, 5] (fun x G => by simp [forall_fin_succ, yk, jr, funext_iff, sum_univ_succ] at G ⊢; grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr]) (by omega) 1
      convert (Submodule.mem_inf.1 this).1 using 1; funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [vM, jx, kt]
    have hKb : finrank KD (K ⊓ ker x4 : Submodule KD ze) ≤ 2 := (Submodule.finrank_mono fun T H => by
      obtain ⟨hTL, e⟩ := Ql.1 H.1
      have := hK0 T H.1; have hp := (qb J hTL).1; have hb := mem_ker.1 H.2
      simp [funext_iff, forall_fin_succ, x4, qt] at hb; simp only [qY, sum_prod_type, sum_univ_four] at hp
      by_cases hμ : T (0, 0) + T (3, 0) = 0
      . exact (mem_span_range_iff_exists_fun KD).2 ⟨![(T (1, 0) - T (2, 0)) / 2, (T (0, 0) - T (3, 0)) / 2], by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [sum_univ_succ, y7, vM] <;> grind⟩
      . refine (Kn J O I hB ?_).elim
        convert L.smul_mem (2 / (T (0, 0) + T (3, 0))) (L.sub_mem (L.sub_mem hTL (L.smul_mem ((T (1, 0) - T (2, 0)) / 2) I)) (L.smul_mem ((T (0, 0) - T (3, 0)) / 2) hB)) using 1
        funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [y7, vM, Jl] <;> field_simp <;> grind).trans ((finrank_range_le_card ![y7, vM]).trans (by simp))
    have hW : K.map x4 ⊔ span KD {fun _ => (1 : KD)} = ⊤ := by
      have h0 : K.map x4 ⊓ span KD {fun _ => (1 : KD)} = ⊥ := by
        rw [Submodule.eq_bot_iff]; rintro v ⟨⟨T, H, rfl⟩, hv⟩
        obtain ⟨c, hc⟩ := mem_span_singleton.1 hv
        obtain ⟨hTL, e⟩ := Ql.1 H
        have := congrFun hc; simp [forall_fin_succ, x4, qt] at this
        rw [← hc, show c = 0 by have := Zd J hTL 1 2 (l := c / 2) (by grind); grind, zero_smul]
      have h1 := finrank_sup_add_finrank_inf_eq (K.map x4) (span KD {fun _ => (1 : KD)})
      rw [h0, finrank_bot, finrank_span_singleton fun h => by simpa using congrFun h 0] at h1
      have := zW x4 K
      apply eq_top_of_finrank_eq
      have := Submodule.finrank_le (K.map x4 ⊔ span KD {fun _ => (1 : KD)})
      rw [finrank_fin_fun] at this ⊢; omega
    have hBc := fun T (H : T ∈ L) => k6 (zH J (wk ![1, 0, 3, 2] (by decide)) 1) ⟨vM, hB, by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [yD, vM, y7, wk]⟩ (mem_map_of_mem H)
    have hr0 : ∀ T ∈ L, T (0, 1) = T (3, 1) /\ T (0, 2) = T (3, 2) /\ T (0, 3) = T (3, 3) := fun T H => by
      let φ : (Fin 3 -> KD) →ₗ[KD] KD := (T (0, 1) - T (3, 1)) • proj 0 + (T (0, 2) - T (3, 2)) • proj 1 + (T (0, 3) - T (3, 3)) • proj 2
      have q0 := hBc T H; simp [yD, wk] at q0
      have hle : K.map x4 ⊔ span KD {fun _ => (1 : KD)} ≤ ker φ := sup_le (by
        rintro _ ⟨T', H', rfl⟩
        have := hK0 T' H'; have q1 := hBc _ (L.add_mem H H'.1); simp [yD, wk] at q1
        simp [φ, x4, qt]; grind) (by simp [φ]; grind)
      have f := fun v => mem_ker.1 (hle (hW ▸ mem_top (x := v)))
      have f0 := f (single 0 1); have f1 := f (single 1 1); have f2 := f (single 2 1)
      simp [φ] at f0 f1 f2; grind
    obtain ⟨T, h3, u⟩ := S ![1, 1, -2] (by norm_num)
    have hk0 : κ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by have := hr0 T h3; have := M T h3; have := (k6 J I h3).2.2; simp at u; grind)
    have := (yU (wz J) (jx ∘ₗ pi ![zS 0, zS 1, zS 2, zS 3, zS 4, 0, 0, 0, 0, 0, 0, zS 5, zS 6, zS 7]) (fun T H => vQ J I H (yA T ∘ ![0, 1, 2, 3, 4, 11, 12, 13]) (by have := hr0 T H; have := M T H; have := Zd J H 0 3 (l := T (0, 3)) (by grind); simp [funext_iff, forall_fin_succ, yA]; grind)) ![single 4 1, single 7 1] ![4, 7] fun x G => by simp [forall_fin_succ, yk, jr, funext_iff, sum_univ_succ] at G ⊢; grind).1
    omega
  push Not at hC
  obtain ⟨T', H', hne⟩ := hC
  obtain ⟨H', e⟩ := Ql.1 H'
  obtain ⟨κ, M⟩ := ZU J I S
  have F : ∀ T ∈ L, (T (1, 1) - T (2, 1)) * (T' (0, 2) - T' (3, 2)) * (T' (0, 3) - T' (3, 3)) + (T (1, 2) - T (2, 2)) * (T' (0, 1) - T' (3, 1)) * (T' (0, 3) - T' (3, 3)) + (T (1, 3) - T (2, 3)) * (T' (0, 1) - T' (3, 1)) * (T' (0, 2) - T' (3, 2)) = 0 /\ (T (0, 1) - T (3, 1)) * ((T (1, 2) - T (2, 2)) * (T' (0, 3) - T' (3, 3)) + (T (1, 3) - T (2, 3)) * (T' (0, 2) - T' (3, 2))) + (T (0, 2) - T (3, 2)) * ((T (1, 1) - T (2, 1)) * (T' (0, 3) - T' (3, 3)) + (T (1, 3) - T (2, 3)) * (T' (0, 1) - T' (3, 1))) + (T (0, 3) - T (3, 3)) * ((T (1, 1) - T (2, 1)) * (T' (0, 2) - T' (3, 2)) + (T (1, 2) - T (2, 2)) * (T' (0, 1) - T' (3, 1))) = 0 := fun T H => by
    obtain ⟨hs0, hQ, hF⟩ := k6 J I H
    have hFp := (k6 J I (L.add_mem H H')).2.2; have hFm := (k6 J I (L.sub_mem H H')).2.2
    obtain ⟨s1, s2⟩ := M T' H'
    have e1 : T' (3, 1) = T' (0, 3) + T' (3, 3) - T' (0, 1) := by grind
    have e2 : T' (3, 2) = T' (0, 3) + T' (3, 3) - T' (0, 2) := by grind
    have e3 : T (2, 3) = T (1, 1) - T (2, 1) + T (1, 2) - T (2, 2) + T (1, 3) := by grind
    simp only [Pi.add_apply, Pi.sub_apply, ← e.1, ← e.2.1, ← e.2.2, e1, e2, e3] at hFp hFm hF hQ ⊢
    exact ⟨by linear_combination 2 * hF - hFp - hFm, by linear_combination hFm - hFp - (T' (0, 3) + T' (3, 3)) * hQ⟩
  obtain ⟨T1, hT1, a⟩ := S ![1, 0, -1] (by simp)
  obtain ⟨T2, hT2, b⟩ := S ![0, 1, -1] (by simp)
  simp at a b
  have r1 : (T' (0, 2) - T' (3, 2)) * (T' (0, 3) - T' (3, 3) - (T' (0, 1) - T' (3, 1))) = 0 := by grind [(F T1 hT1).1]
  have r2 : (T' (0, 1) - T' (3, 1)) * (T' (0, 3) - T' (3, 3) - (T' (0, 2) - T' (3, 2))) = 0 := by grind [(F T2 hT2).1]
  rcases mul_eq_zero.1 r1 with r1 | r1 <;> rcases mul_eq_zero.1 r2 with r2 | r2
  . refine ZV (zH J 1 (wk ![0, 3, 2, 1] (by decide))) (by rw [zF, O]) ⟨y7, I, by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [yD, y7, wk]⟩ (fun x G => ?_) ?_
    . obtain ⟨T, H, a⟩ := S ![x 2, x 1, x 0] (by simp; grind)
      exact ⟨_, mem_map_of_mem H, by simp [yD, wk] at a ⊢; grind⟩
    . rintro _ ⟨T, H, rfl⟩; simp [yD, wk]; grind [(F T H).2]
  . exact ZV J O I S fun T H => by grind [(F T H).2]
  . refine ZV (zH J 1 (wk ![0, 2, 1, 3] (by decide))) (by rw [zF, O]) ⟨y7, I, by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [yD, y7, wk]⟩ (fun x G => ?_) ?_
    . obtain ⟨T, H, a⟩ := S ![x 1, x 0, x 2] (by simp; grind)
      exact ⟨_, mem_map_of_mem H, by simp [yD, wk] at a ⊢; grind⟩
    . rintro _ ⟨T, H, rfl⟩; simp [yD, wk]; grind [(F T H).2]
  . have hK4 := zW wh L
    obtain ⟨κ', M'⟩ := YB S (qt (0, 2) - qt (3, 2) - (qt (0, 3) - qt (3, 3))) (qt (0, 1) - qt (3, 1) - (qt (0, 3) - qt (3, 3))) fun T H => by simp [qt]; grind [(F T H).2, (k6 J I H).1]
    simp [qt] at M'
    have hkk : κ' ^ 2 = κ ^ 2 := by obtain ⟨T, h3, u⟩ := S ![1, 1, -2] (by norm_num); simp at u; grind [M T h3, M' T h3, (k6 J I h3).2.2]
    have P : ∀ T ∈ L, ∃ x, (jx ∘ₗ v6 κ κ') x = T := fun T H => vQ J I H (yA T ∘ ![0, 1, 2, 3, 4, 7, 10, 11, 12, 13]) (by simp [funext_iff, forall_fin_succ, v6, yA]; grind [M T H, M' T H])
    by_cases hD : 3 + 4 * κ ^ 2 = 0
    . have hX := (yU (wz J) _ P ![single 4 1, ![0, 0, 0, 0, 0, κ / 3, κ' / 3, 1, 0, 0], ![0, 0, 0, 0, 0, -κ / 3, -κ' / 3, 0, 1, 0]] ![4, 7, 8] (fun x G => by simp [forall_fin_succ, yk, jr, v6] at G; funext i; fin_cases i <;> simp [sum_univ_succ] <;> grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr, v6] <;> grind) (by omega)
      have := (yU (U := L ⊓ ker wh) (fun T H => wz J T H.1) (jx ∘ₗ pi ![-zS 2, -zS 2, -zS 2, zS 0, zS 1, zS 2, zS 2, zS 2, zS 3, zS 3, zS 3, 0, 0, zS 4]) (fun T H => by
          obtain ⟨H, e1, e2, e3⟩ := Ql.1 H; have := M T H; have := M' T H
          have f1 : T (0, 1) = T (0, 3) := by grind
          have f2 : T (0, 2) = T (0, 3) := by grind
          have f3 : T (3, 1) = T (3, 3) := by grind
          have f4 : T (3, 2) = T (3, 3) := by grind
          have : T (1, 1) = T (1, 2) /\ T (1, 2) = T (1, 3) := by
            have p1 := v8 J (L.add_mem (hX 1) H); have m1 := v8 J (L.sub_mem (hX 1) H); have p2 := v8 J (L.add_mem (hX 2) H); have m2 := v8 J (L.sub_mem (hX 2) H); have p3 := v8 J (L.add_mem (L.add_mem (hX 1) (hX 2)) H); have u := v8 J H
            simp [jh, zs, z8, sum_univ_four, jx, kt, v6, ← e1, ← e2, ← e3, f1, f2, f3, f4] at p1 m1 p2 m2 p3 u
            exact ⟨by linear_combination (-1 / 8) * p1 + (1 / 8) * m1 + (1 / 8) * p2 + (-1 / 8) * m2 + (T (1, 1) / 3 - T (1, 2) / 3) * hkk + (T (1, 1) / 3 - T (1, 2) / 3) * hD, by linear_combination (-1 / 4) * p1 + (-3 / 8) * p2 + (1 / 8) * m2 + (1 / 4) * p3 + (1 / 2) * u + (T (1, 2) / 3 - T (1, 3) / 3) * hkk + (T (1, 2) / 3 - T (1, 3) / 3) * hD⟩
          have := Zd J H 1 2 (l := T (1, 1)) (by grind)
          exact vQ J I H (yA T ∘ ![3, 4, 7, 10, 13]) (by simp [funext_iff, forall_fin_succ, yA]; grind)) ![![0, 1, 0, 0, 0]] ![1] fun x G => by simp [forall_fin_succ, yk, jr, funext_iff] at G ⊢; grind).1
      omega
    . have := (yU (wz J) _ P ![single 4 1] ![4] fun x G => by simp [forall_fin_succ, yk, jr, v6, funext_iff] at G ⊢; grind).1
      omega
theorem Jq (D : ∀ k, z k ≠ 0) (C : Jm L z) : (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 ≠ 0 -> False) /\ (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 0 -> (¬ kC L) -> vO (fun k => z k / 2) ∈ L) := by
  obtain ⟨hz3, hzs⟩ := Jo J I C
  have ht := ZT C
  obtain ⟨hY2, hY1⟩ := Kz J D hz3 hzs
  set Y := L.map kj
  let f : (Fin 6 -> KD) →ₗ[KD] KD := (proj 0 : (Fin 6 -> KD) →ₗ[KD] KD) + proj 1 + proj 2 - proj 3 - proj 4 - proj 5
  have hf : ∀ T, f (kj T) = T (0, 1) - T (3, 1) + (T (0, 2) - T (3, 2)) + (T (0, 3) - T (3, 3)) := fun T => by simp [f, kj, qt]; ring
  have cA : (¬ kC L) -> ∃ ya yb : Fin 6 -> KD, ya 0 + ya 1 + ya 2 - ya 3 - ya 4 - ya 5 = 1 /\ yb 0 + yb 1 + yb 2 - yb 3 - yb 4 - yb 5 = 0 /\ ∀ T ∈ L, ∃ x, (jx ∘ₗ jt z ya yb) x = T := fun Q => by
    obtain ⟨Ta, hTa, hne⟩ := not_forall₂.1 Q; rw [← hf] at hne
    set ya := (f (kj Ta))⁻¹ • kj Ta
    have hya : f ya = 1 := by simp only [ya, map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hne
    have hyaY : ya ∈ Y := Y.smul_mem _ (mem_map_of_mem hTa)
    obtain ⟨yb, hybN, hyb⟩ := vN (Y ⊓ ker f) (by have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => by have := mem_ker.1 (h ▸ hyaY : ya ∈ Y ⊓ ker f).2; rw [hya] at this; exact one_ne_zero this); omega)
    refine ⟨ya, yb, by simpa [f] using hya, by simpa [f] using mem_ker.1 hybN.2, fun T H => ?_⟩
    obtain ⟨β, hβ⟩ := hyb (kj T - f (kj T) • ya) ⟨Y.sub_mem (mem_map_of_mem H) (Y.smul_mem _ hyaY), mem_ker.2 (by rw [map_sub, map_smul, hya, smul_eq_mul, mul_one, sub_self])⟩
    generalize f (kj T) = α at hβ
    have e := congrFun hβ; obtain ⟨t, b⟩ := ht T H
    simp [forall_fin_succ, kj, qt] at e
    exact vQ J I H ![yA T 0, yA T 1, yA T 2, yA T 3, yA T 4, t, yA T 13, α, β] (by simp [funext_iff, forall_fin_succ, jt, yA]; grind)
  refine ⟨fun hzz => ?_, fun hzz Q => ?_⟩
  . by_cases Q : kC L
    . obtain ⟨yb, -, hyb⟩ := vN Y (hY1 Q hzz)
      have := (yU (wz J) (jx ∘ₗ wl z yb) (fun T H => by
        obtain ⟨β, hβ⟩ := hyb _ (mem_map_of_mem H); obtain ⟨t, b⟩ := ht T H
        have := congrFun hβ; simp [forall_fin_succ, kj, qt] at this
        exact vQ J I H ![yA T 0, yA T 1, yA T 2, yA T 3, yA T 4, t, yA T 13, β] (by simp [funext_iff, forall_fin_succ, wl, yA]; grind)) ![single 4 1, single 6 1, single 7 1] ![4, 6, 7] fun x G => by simp [forall_fin_succ, yk, jr, wl, funext_iff, sum_univ_succ] at G ⊢; grind).1
      omega
    . obtain ⟨ya, yb, hya, hyb, P⟩ := cA Q
      exact (Jp J O hz3 hya hyb P).1 hzz
  . obtain ⟨ya, yb, hya, hyb, P⟩ := cA Q
    convert (Jp J O hz3 hya hyb P).2 hzz using 1; funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [vO, jx, kt, jt] <;> grind
theorem Jr (hz0 : z 0 = 1) (hz3 : z 0 + z 1 + z 2 = 0) (hzz : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 0) (ht : ZS L z) (hzs : ∀ T ∈ L, z 0 * (T (0, 1) + T (3, 1)) + z 1 * (T (0, 2) + T (3, 2)) + z 2 * (T (0, 3) + T (3, 3)) = 0) (hrr : kC L) (hwq : ∀ T ∈ L, z 0 * T (3, 1) + z 2 * T (3, 2) + z 1 * T (3, 3) = 0) : vO (fun k => z k / 2) ∈ L := by
  have P : ∀ T ∈ L, ∃ x, (jx ∘ₗ vP z) x = T := fun T H => by
    obtain ⟨t, b⟩ := ht T H; have := hrr T H; have := hzs T H; have := hwq T H
    exact vQ J I H ![yA T 0, yA T 1, yA T 2, yA T 3, yA T 4, t, yA T 13, (T (3, 1) + T (3, 2) + T (3, 3)) / 3, (T (0, 1) + z 2 * T (0, 2) + z 1 * T (0, 3)) / 3, (T (0, 1) + z 1 * T (0, 2) + z 2 * T (0, 3)) / 3] (by simp [funext_iff, forall_fin_succ, vP, yA]; grind)
  convert (yU (wz J) _ P ![single 4 1, single 5 1, single 6 1] ![4, 5, 6] (fun x G => by simp [forall_fin_succ, yk, jr, vP, funext_iff, sum_univ_succ] at G ⊢; grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr, vP] <;> grind) (by omega) 1 using 1
  funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [vO, jx, kt, vP] <;> grind
theorem YJ (hz0 : z 0 = 1) (hz3 : z 0 + z 1 + z 2 = 0) (hzz : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 0) (ht : ZS L z) (hzs : xn L z) (hrr : kC L) : vO (fun k => z k / 2) ∈ L := by
  rcases zz L (qt (0, 1) + z 2 • qt (0, 2) + z 1 • qt (0, 3)) (qt (3, 1) + z 2 • qt (3, 2) + z 1 • qt (3, 3)) (fun T H => by simp [qt]; grind [hzs T H, hrr T H]) with hp | hq
  . obtain ⟨X, hX, e⟩ := Jr (L := L.map (zq (wk ![3, 1, 2, 0] (by decide)) 1 : ze →ₗ[KD] ze)) (zH J _ _) (by rw [zF, O]) ⟨y7, I, by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [yD, wk, y7]⟩ hz0 hz3 hzz (by rintro _ ⟨T, H, rfl⟩; obtain ⟨t, b⟩ := ht T H; exact ⟨t, by simpa [yD, wk] using b⟩) (by rintro _ ⟨T, H, rfl⟩; simp [yD, wk]; grind [(hzs T H).1]) (by rintro _ ⟨T, H, rfl⟩; simp [yD, wk]; grind [hrr T H]) (by rintro _ ⟨T, H, rfl⟩; have := hp T H; simp [qt] at this; simp [yD, wk]; grind)
    rw [show vO (fun k => z k / 2) = X by funext ⟨i, j⟩; have := congrFun e (wk ![3, 1, 2, 0] (by decide) i, j); fin_cases i <;> fin_cases j <;> simp [yD, wk, vO] at this ⊢ <;> grind]; exact hX
  . exact Jr J O I hz0 hz3 hzz ht (fun T H => (hzs T H).1) hrr fun T H => by have := hq T H; simp [qt] at this; grind
set_option maxHeartbeats 3000000 in
theorem YK (D : ∀ k, z k ≠ 0) (hz0 : z 0 = 1) (C : Jm L z) (hzz : z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 0) : False := by
  obtain ⟨hz3, hzs⟩ := Jo J I C
  have ht := ZT C
  obtain ⟨n, l, hn, hrep⟩ := YF J D hz0 hz3 hzz hzs (by
    by_cases Q : kC L
    . exact YJ J O I hz0 hz3 hzz ht hzs Q
    . exact (Jq J O I D C).2 hzz Q)
  by_cases hn0 : n = 0
  . subst hn0
    have := (yU (wz J) (jx ∘ₗ pi ![zS 0, zS 1, zS 2, zS 3, zS 4, 0, 0, 0, 0, 0, 0, (z 0 / 2) • zS 5, (z 1 / 2) • zS 5, zS 6]) (fun T H => by
      obtain ⟨t, b⟩ := ht T H; obtain ⟨c, r⟩ := hrep T H; simp at r
      have := Zd J H 0 3 (l := c * l / 2) (by grind)
      exact vQ J I H ![yA T 0, yA T 1, yA T 2, yA T 3, yA T 4, t, yA T 13] (by simp [funext_iff, forall_fin_succ, yA]; grind)) ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]] ![4, 5, 6] fun x G => by simp [forall_fin_succ, yk, jr, funext_iff, sum_univ_succ] at G ⊢; grind).1
    omega
  set yb : Fin 6 -> KD := ![(l + n 0) / 2, (l + n 1) / 2, (l + n 2) / 2, (l - n 0) / 2, (l - n 1) / 2, (l - n 2) / 2]
  have P : ∀ T ∈ L, ∃ x, (jx ∘ₗ wl z yb) x = T := fun T H => by
    obtain ⟨t, b⟩ := ht T H; obtain ⟨c, r⟩ := hrep T H
    exact vQ J I H ![yA T 0, yA T 1, yA T 2, yA T 3, yA T 4, t, yA T 13, c] (by simp [funext_iff, forall_fin_succ, wl, yA, yb]; grind)
  by_cases hf : n 0 + n 1 + n 2 = 0
  swap
  . have := (yU (wz J) _ P ![single 4 1, single 5 1] ![4, 5] fun x G => by simp [forall_fin_succ, yk, jr, wl, yb, funext_iff, sum_univ_succ] at G ⊢; grind).1
    omega
  have hn1 : n 1 = z 2 * n 0 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by simp [jE] at hn; grind))
  have hn2 : n 2 = z 1 * n 0 := by grind
  have hn00 : n 0 ≠ 0 := fun h => hn0 (funext fun i => by fin_cases i <;> simp [h, hn1, hn2])
  have hl : l = 0 := by
    by_contra hl
    have := (yU (wz J) _ P ![single 4 1, single 5 1, single 6 1] ![4, 5, 6] fun x G => by simp [forall_fin_succ, yk, jr, wl, yb, funext_iff, sum_univ_succ] at G ⊢; grind).1
    omega
  have hct := (yU (wz J) _ P ![single 4 1, single 5 1, single 6 1, single 7 1] ![4, 5, 6, 7] (fun x G => by simp [forall_fin_succ, yk, jr, wl, yb, funext_iff, sum_univ_succ] at G ⊢; grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr, wl, yb] <;> grind) (by omega)
  have hzb : ∀ T ∈ L, z 1 * (T (1, 1) + T (2, 1)) + z 2 * (T (1, 2) + T (2, 2)) + (T (1, 3) + T (2, 3)) = 0 := fun T H => by
    have := Jn (zH J (wk ![1, 0, 3, 2] (by decide)) 1) (y := ![n 0 / 2, n 0 * z 2 / 2, n 0 * z 1 / 2]) (by simp; grind) (by simp; grind) (by simp [hn00, D]) ⟨_, hct 3, by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [yD, wk, vO, jx, kt, wl, yb] <;> grind⟩ (mem_map_of_mem H)
    simp [yD, wk] at this; grind
  have P' : ∀ T ∈ L, ∃ x, (jx ∘ₗ km z (n 0)) x = T := fun T H => by
    obtain ⟨t, b⟩ := ht T H; obtain ⟨c, r⟩ := hrep T H; have := hzb T H
    exact vQ J I H ![(T (1, 1) + T (2, 1) + (T (1, 2) + T (2, 2)) + (T (1, 3) + T (2, 3))) / 6, (T (1, 1) + T (2, 1) + z 2 * (T (1, 2) + T (2, 2)) + z 1 * (T (1, 3) + T (2, 3))) / 6, yA T 3, yA T 4, t, yA T 13, c] (by funext i; fin_cases i <;> simp [km, yA] <;> grind)
  have hct' := (yU (wz J) _ P' ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]] ![1, 3, 4, 5, 6] (fun x G => by simp [forall_fin_succ, yk, jr, km, funext_iff, sum_univ_succ] at G ⊢; grind)).2 (fun i y => by fin_cases i <;> simp [yk, jr, km] <;> grind) (by omega)
  have hLe := eq_of_le_of_finrank_le (fun T H => by
    obtain ⟨x, rfl⟩ := P' T H
    have h0 : x 0 = 0 := Zd J (L.sub_mem H (L.add_mem (L.add_mem (L.add_mem (L.add_mem (L.smul_mem (x 1) (hct' 0)) (L.smul_mem (x 3) (hct' 1))) (L.smul_mem (x 4) (hct' 2))) (L.smul_mem (x 5) (hct' 3))) (L.smul_mem (x 6) (hct' 4)))) 1 2 (by simp [jx, kt, km]; grind)
    exact (mem_span_range_iff_exists_fun KD).2 ⟨fun i : Fin 6 => x i.succ, by simp only [← map_smul, ← map_sum]; congr 1; funext j; fin_cases j <;> simp [sum_univ_succ, h0]⟩ : L ≤ span KD (Set.range fun i : Fin 6 => (jx ∘ₗ km z (n 0)) (single i.succ 1))) ((finrank_range_le_card _).trans (by simp [O]))
  exact Kn J O I (by convert hct 2 using 1; funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [vM, jx, kt, wl]) (by convert L.smul_mem (-1) (hLe ▸ subset_span ⟨1, rfl⟩ : (jx ∘ₗ km z (n 0)) (single 2 1) ∈ L) using 1; funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [Jl, jx, kt, km])
theorem wX :
    (∀ T ∈ L, ∀ k : Fin 3, T (1, k.succ) = T (2, k.succ)) \/
    ∃ c : Fin 3, ∀ T ∈ L, T (1, c.succ) = T (2, c.succ) /\
      T (1, (z6 c 0).succ) - T (2, (z6 c 0).succ) =
        -(T (1, (z6 c 1).succ) - T (2, (z6 c 1).succ)) := by
  obtain ⟨hM2, -⟩ := YG J I
  rcases (by omega : finrank KD (L.map wh) = 0 \/ finrank KD (L.map wh) = 1 \/ finrank KD (L.map wh) = 2) with h0 | h1 | h2
  . left; intro T H k
    have := congrFun ((Submodule.mem_bot KD).1 (Submodule.finrank_eq_zero.1 h0 ▸ mem_map_of_mem H)) k
    simp [wh, qt] at this; grind
  . obtain ⟨z, hzM, D⟩ := vN _ h1.le
    by_cases hall : ∀ k, z k ≠ 0
    . have C' : Jm L ((z 0)⁻¹ • z) := ⟨Submodule.smul_mem _ _ hzM, fun x G => by obtain ⟨c, rfl⟩ := D x G; exact ⟨c * z 0, by rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hall 0), mul_one]⟩⟩
      have D' : ∀ k, ((z 0)⁻¹ • z) k ≠ 0 := fun k => by simp [hall]
      by_cases hzz : ((z 0)⁻¹ • z) 0 ^ 2 + ((z 0)⁻¹ • z) 1 ^ 2 + ((z 0)⁻¹ • z) 2 ^ 2 = 0
      . exact (YK J O I D' (by simp [hall 0]) C' hzz).elim
      . exact ((Jq J O I D' C').1 hzz).elim
    push Not at hall; obtain ⟨c, hc⟩ := hall
    right; refine ⟨c, fun T H => ?_⟩
    obtain ⟨t, ht⟩ := D _ (mem_map_of_mem H)
    have e := congrFun ht; have := (k6 J I H).1
    simp [forall_fin_succ, wh, qt] at e
    fin_cases c <;> simp [z6] at hc ⊢ <;> grind
  . exact (YI J O I h2).elim
theorem kT
    (hr0 : finrank KD (L.map (z9 0)) = 3)
    (hne : ¬ ∀ T ∈ L, ∀ k : Fin 3, T (1, k.succ) = T (2, k.succ)) :
    ∃ c : Fin 3, ∀ T ∈ L, T (1, c.succ) = T (2, c.succ) /\ T (0, c.succ) = T (3, c.succ) /\
      T (0, (z6 c 0).succ) + T (3, (z6 c 0).succ) =
        T (0, (z6 c 1).succ) + T (3, (z6 c 1).succ) := by
  rcases wX J O I with h | ⟨c, hc⟩
  . exact (hne h).elim
  refine ⟨c, fun T H => ⟨(hc T H).1, YH J I hr0 (a := (z6 c 0).succ) (b := (z6 c 1).succ) (by fin_cases c <;> decide) (fun T H => (hc T H).1) (fun T H => (hc T H).2) ?_ T H⟩⟩
  by_contra hcon; push Not at hcon
  exact hne fun T H k => by have h1 := hc T H; have h3 := hcon T H; fin_cases c <;> fin_cases k <;> simp [z6] at h1 h3 ⊢ <;> grind
end
section
include J O
theorem Js (p : Equiv.Perm (Fin 4)) {r0 : Fin 4} (hE : (fun x : Fin 4 × Fin 4 => if x = (r0, p 1) then (1 : KD) else if x = (r0, p 2) then -1 else 0) ∈ L) : zg (Qm L p r0) /\ finrank KD (Qm L p r0) = 6 /\ y7 ∈ Qm L p r0 /\ (∀ T ∈ L, zq p (Equiv.swap 0 r0) (zM T) ∈ Qm L p r0) /\ (∀ i, i ≠ r0 -> ∃ k : Fin 3, Equiv.swap 0 r0 k.succ = i) /\ ∀ k : Fin 3, Equiv.swap 0 r0 k.succ ≠ r0 := by
  refine ⟨zH (zX J) _ _, by rw [zF, zT, O], ⟨_, ⟨_, hE, rfl⟩, ?_⟩, fun T H => ⟨_, ⟨T, H, rfl⟩, rfl⟩, fun i hi => ?_, fun k hk => ?_⟩
  . funext ⟨i, j⟩
    simp only [LinearEquiv.coe_coe, yD, zQ, y7, Prod.mk.injEq]
    simp only [show Equiv.swap 0 r0 j = r0 ↔ j = 0 by rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right], p.injective.eq_iff]
    fin_cases i <;> fin_cases j <;> simp
  . obtain ⟨k, hk⟩ := Fin.exists_succ_eq.2 (fun h => hi (by rw [Equiv.symm_apply_eq] at h; rw [h, Equiv.swap_apply_left]) : (Equiv.swap 0 r0).symm i ≠ 0)
    exact ⟨k, by rw [hk, Equiv.apply_symm_apply]⟩
  . rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hk; exact Fin.succ_ne_zero k hk
theorem YL (p : Equiv.Perm (Fin 4)) {r0 : Fin 4} (hE : (fun x : Fin 4 × Fin 4 => if x = (r0, p 1) then (1 : KD) else if x = (r0, p 2) then -1 else 0) ∈ L) (h0 : ¬ ∀ T ∈ L, T (0, p 1) = T (0, p 2)) (Q : r0 ≠ 0) : ∃ i, i ≠ r0 /\ ∀ T ∈ L, T (i, p 1) = T (i, p 2) /\ ∀ i' i'', i' ≠ r0 -> i'' ≠ r0 -> i' ≠ i -> i'' ≠ i -> i' ≠ i'' -> T (i', p 1) - T (i', p 2) = -(T (i'', p 1) - T (i'', p 2)) := by
  obtain ⟨J', O', I', mem, hk, hk0⟩ := Js J O p hE
  rcases wX J' O' I' with h | ⟨c, hc⟩
  . exact (h0 fun T H => by obtain ⟨k, hk⟩ := hk 0 Q.symm; simpa [yD, zQ, hk] using h _ (mem T H) k).elim
  refine ⟨Equiv.swap 0 r0 c.succ, hk0 c, fun T H => ⟨by simpa [yD, zQ] using (hc _ (mem T H)).1, fun i' i'' h1 h2 h3 h4 h5 => ?_⟩⟩
  obtain ⟨k', rfl⟩ := hk i' h1; obtain ⟨k'', rfl⟩ := hk i'' h2
  have e := (hc _ (mem T H)).2; simp only [yD, zQ] at e
  rcases (by decide : ∀ c k k' : Fin 3, k ≠ c -> k' ≠ c -> k ≠ k' -> (k = z6 c 0 /\ k' = z6 c 1) \/ (k = z6 c 1 /\ k' = z6 c 0)) c k' k'' (fun h => h3 (by rw [h])) (fun h => h4 (by rw [h])) (fun h => h5 (by rw [h])) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  . exact e
  . linear_combination e
theorem YM (p : Equiv.Perm (Fin 4)) {r0 : Fin 4} (hE : (fun x : Fin 4 × Fin 4 => if x = (r0, p 1) then (1 : KD) else if x = (r0, p 2) then -1 else 0) ∈ L) (hc0 : finrank KD (L.map (zD (p 0))) = 3) (h0 : ¬ ∀ T ∈ L, T (0, p 1) = T (0, p 2)) (Q : r0 ≠ 0) : ∃ i, i ≠ r0 /\ ∀ T ∈ L, T (i, p 1) = T (i, p 2) /\ T (i, p 0) = T (i, p 3) /\ ∀ i' i'', i' ≠ r0 -> i'' ≠ r0 -> i' ≠ i -> i'' ≠ i -> T (i', p 0) + T (i', p 3) = T (i'', p 0) + T (i'', p 3) := by
  obtain ⟨J', O', I', mem, hk, hk0⟩ := Js J O p hE
  obtain ⟨c, hc⟩ := kT J' O' I' (by rw [show (Qm L p r0).map (z9 0) = (L.map (zD (p 0))).map (LinearEquiv.funCongrLeft KD KD (Equiv.swap 0 r0) : (Fin 4 -> KD) →ₗ[KD] (Fin 4 -> KD)) by simp only [Qm, ← Submodule.map_comp]; congr 1, LinearEquiv.finrank_map_eq, hc0]) fun h => h0 fun T H => by obtain ⟨k, hk⟩ := hk 0 Q.symm; simpa [yD, zQ, hk] using h _ (mem T H) k
  refine ⟨Equiv.swap 0 r0 c.succ, hk0 c, fun T H => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hc _ (mem T H)
  simp only [yD, zQ] at e1 e2 e3
  refine ⟨e1, e2, fun i' i'' h1 h2 h3 h4 => ?_⟩
  obtain ⟨k', rfl⟩ := hk i' h1; obtain ⟨k'', rfl⟩ := hk i'' h2
  have g : ∀ k : Fin 3, k ≠ c -> T (Equiv.swap 0 r0 k.succ, p 0) + T (Equiv.swap 0 r0 k.succ, p 3) = T (Equiv.swap 0 r0 (z6 c 0).succ, p 0) + T (Equiv.swap 0 r0 (z6 c 0).succ, p 3) := fun k hk => by
    rcases jk c k with h | h | h
    . exact (hk h).elim
    . rw [h]
    . rw [h]; exact e3.symm
  rw [g k' (fun h => h3 (by rw [h])), g k'' (fun h => h4 (by rw [h]))]
set_option maxHeartbeats 1000000 in
theorem YN (s1 : ∀ T ∈ L, T (2, 1) = T (2, 2)) (s2 : ∀ T ∈ L, T (2, 0) = T (2, 3)) (s3 : ∀ T ∈ L, T (0, 1) - T (0, 2) = -(T (1, 1) - T (1, 2))) (s4 : ∀ T ∈ L, T (0, 0) + T (0, 3) = T (1, 0) + T (1, 3)) : False := by
  let φ : ze →ₗ[KD] Fin 2 -> KD := pi ![qt (2, 0), qt (2, 1)]
  have hR : finrank KD (L.map φ) ≤ 1 := by
    by_contra h; push Not at h
    obtain ⟨T, H, e⟩ : (fun _ => (1 : KD)) ∈ L.map φ := (eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (by rw [finrank_fin_fun]; omega)) : L.map φ = ⊤) ▸ mem_top
    have := congrFun e; simp [forall_fin_succ, φ, qt] at this
    exact qg J 2 ⟨T, H, funext fun j => by have := s1 T H; have := s2 T H; fin_cases j <;> simp [zA] <;> grind⟩
  obtain ⟨y, -, hy⟩ := vN _ hR
  obtain ⟨a0, a1, ha, hrep⟩ : ∃ a0 a1 : KD, (a0 ≠ 0 \/ a1 ≠ 0) /\ ∀ T ∈ L, ∃ c : KD, T (2, 0) = c * a0 /\ T (2, 1) = c * a1 := by
    by_cases hy0 : y = 0
    . refine ⟨0, 1, Or.inr one_ne_zero, fun T H => ⟨0, ?_⟩⟩
      obtain ⟨c, hc⟩ := hy _ (mem_map_of_mem H); have := congrFun hc; simp [forall_fin_succ, φ, qt, hy0] at this; simp [this]
    . refine ⟨y 0, y 1, ?_, fun T H => ?_⟩
      . by_contra h; push Not at h; exact hy0 (funext fun i => by fin_cases i <;> simp [h.1, h.2])
      . obtain ⟨c, hc⟩ := hy _ (mem_map_of_mem H); have := congrFun hc; simp [forall_fin_succ, φ, qt] at this; exact ⟨c, this⟩
  have P : ∀ T ∈ L, ∃ x, Zc a0 a1 x = T := fun T H => by
    obtain ⟨c, r0, r1⟩ := hrep T H
    have := s1 T H; have := s2 T H; have := s3 T H; have := s4 T H; have hP := (qb J H).1; simp only [qY, sum_prod_type, sum_univ_four] at hP
    exact ⟨![(T (0, 0) + T (0, 3)) / 2, (T (0, 0) - T (0, 3)) / 2, (T (0, 1) + T (0, 2)) / 2, (T (0, 1) - T (0, 2)) / 2, (T (1, 0) - T (1, 3)) / 2, (T (1, 1) + T (1, 2)) / 2, c, T (3, 0), (T (3, 1) + T (3, 2)) / 2, (T (3, 1) - T (3, 2)) / 2], by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> simp [Zc] <;> grind⟩
  set Z : Fin 10 -> KD := ![-5 / 12 * a0 + 1 / 12 * a1, 0, 1 / 12 * a0 - 5 / 12 * a1, 0, 0, 1 / 12 * a0 - 5 / 12 * a1, 1, -5 / 12 * a0 + 1 / 12 * a1, 1 / 12 * a0 - 5 / 12 * a1, 0]
  by_cases hf : 5 * a1 ^ 2 + 22 * a0 * a1 + 5 * a0 ^ 2 = 0
  . have hp := v8 J ((yU (wz J) (Zc a0 a1) P ![single 9 1, Z] ![9, 6] (fun x G => by simp [forall_fin_succ, kS, sum_prod_type, sum_univ_four, Zc] at G; funext i; fin_cases i <;> simp [sum_univ_succ, Z] <;> grind)).2 (fun i y => by fin_cases i <;> simp [kS, sum_prod_type, sum_univ_four, Zc, Z] <;> grind) (by omega) 1)
    simp [jh, zs, z8, sum_univ_four, Zc, Z] at hp
    rcases ha with ha | ha
    . exact ha (pow_eq_zero_iff (n := 4) (by norm_num) |>.1 (by grind))
    . exact ha (pow_eq_zero_iff (n := 4) (by norm_num) |>.1 (by grind))
  . have := (yU (wz J) (Zc a0 a1) P ![single 9 1] ![9] fun x G => by simp [forall_fin_succ, kS, sum_prod_type, sum_univ_four, Zc, funext_iff] at G ⊢; grind).1
    omega
set_option maxHeartbeats 1000000 in
theorem yB
    (hr0 : finrank KD (L.map (z9 0)) = 3) (hc0 : finrank KD (L.map (zD 0)) = 3)
    (H : ∃ T ∈ zm L 0 0, T ≠ 0 /\ (∃ r : Fin 3, ∀ i : Fin 4, ∀ j : Fin 4, i ≠ r.succ -> T (i, j) = 0) /\
      (∃ c : Fin 3, ∀ i : Fin 4, T (i, c.succ) = 0)) : False := by
  obtain ⟨T, hTK, hT0, ⟨r, Q⟩, ⟨c, hc⟩⟩ := H
  have hTL : T ∈ L := hTK.1.1
  have hcol : ∀ i, T (i, 0) = 0 := fun i => by simpa [qF] using congrFun (mem_ker.1 hTK.2.2) i
  obtain ⟨hp0, -, -, hp3⟩ := w9 c
  rw [show z8 0 c = c.succ by fin_cases c <;> rfl] at hp3
  set p := ju c
  set r' := r.succ
  have Q'0 : r' ≠ 0 := Fin.succ_ne_zero r
  have hsum : T (r', p 1) + T (r', p 2) = 0 := by
    have hP := (qb J hTL).1
    rw [qY, sum_prod_type, Finset.sum_eq_single r' (fun i _ hi => Finset.sum_eq_zero fun j _ => Q i j hi) (by simp), ← Equiv.sum_comp p, sum_univ_four, hp0, hp3, hcol, hc] at hP
    simpa using hP
  have hl : T (r', p 1) ≠ 0 := fun h => hT0 (funext fun ⟨i, j⟩ => by
    obtain ⟨k, rfl⟩ := p.surjective j
    by_cases hi : i = r'
    . subst hi; fin_cases k <;> simp [hp0, hp3, hcol, hc, h]; grind
    . exact Q i _ hi)
  have hE : (fun x : Fin 4 × Fin 4 => if x = (r', p 1) then (1 : KD) else if x = (r', p 2) then -1 else 0) ∈ L := by
    convert L.smul_mem (T (r', p 1))⁻¹ hTL using 1
    funext ⟨i, j⟩; obtain ⟨k, rfl⟩ := p.surjective j
    by_cases hi : i = r'
    . subst hi; fin_cases k <;> simp [hp0, hp3, hcol, hc, hl, p.injective.eq_iff] <;> field_simp <;> grind
    . simp [hi, Q i _ hi]
  have h0row : ¬ ∀ T ∈ L, T (0, p 1) = T (0, p 2) := Km J hr0 (p.injective.ne (by decide))
  obtain ⟨ia, hia, I⟩ := YL J O p hE h0row Q'0
  obtain ⟨i, hi, hB⟩ := YM J O p hE (by rw [hp0]; exact hc0) h0row Q'0
  have hi0 : i ≠ 0 := fun h => h0row fun T H => h ▸ (hB T H).1
  have hia0 : ia ≠ 0 := fun h => h0row fun T H => h ▸ (I T H).1
  have hiia : i = ia := by
    by_contra hne
    exact h0row fun T H => by
      have e := (I T H).2 0 i Q'0.symm hi (Ne.symm hia0) hne (Ne.symm hi0)
      rw [(hB T H).1, sub_self, neg_zero] at e
      linear_combination e
  subst hiia
  obtain ⟨σ, hσ0, hσ2, hσ3⟩ := YE r' i Q'0 hi0 hi
  have G : σ 1 ≠ 0 /\ σ 1 ≠ i /\ σ 1 ≠ r' := by rw [← hσ0, ← hσ2, ← hσ3]; exact ⟨σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide)⟩
  refine YN (L := L.map (zq σ p : ze →ₗ[KD] ze)) (zH J σ p) (by rw [zF, O]) ?_ ?_ ?_ ?_ <;> rintro _ ⟨X, hX, rfl⟩ <;> simp only [LinearEquiv.coe_coe, yD, hσ0, hσ2]
  . exact (hB X hX).1
  . exact (hB X hX).2.1
  . exact (I X hX).2 0 (σ 1) Q'0.symm G.2.2 (Ne.symm hi0) G.2.1 (Ne.symm G.1)
  . exact (hB X hX).2.2 0 (σ 1) Q'0.symm G.2.2 (Ne.symm hi0) G.2.1
end
end
section
open Module Submodule Equiv Pi
variable {L:Submodule KD ze} {l:(Fin 4->KD)→ₗ[KD]KD} {A B W W1 W2 X:ze}
def je (a b c d:Fin 4->KD):KD:=a 0*b 1*c 2*d 3+a 0*b 1*c 3*d 2+a 0*b 2*c 1*d 3+a 0*b 2*c 3*d 1+a 0*b 3*c 1*d 2+a 0*b 3*c 2*d 1+a 1*b 0*c 2*d 3+a 1*b 0*c 3*d 2+a 1*b 2*c 0*d 3+a 1*b 2*c 3*d 0+a 1*b 3*c 0*d 2+a 1*b 3*c 2*d 0+a 2*b 0*c 1*d 3+a 2*b 0*c 3*d 1+a 2*b 1*c 0*d 3+a 2*b 1*c 3*d 0+a 2*b 3*c 0*d 1+a 2*b 3*c 1*d 0+a 3*b 0*c 1*d 2+a 3*b 0*c 2*d 1+a 3*b 1*c 0*d 2+a 3*b 1*c 2*d 0+a 3*b 2*c 0*d 1+a 3*b 2*c 1*d 0
def zI (X:ze) (i:Fin 4):Fin 4->KD:=fun j=>X (i,j)
def yM (X Y Z U:ze):KD:=je (zI X 0) (zI Y 1) (zI Z 2) (zI U 3)
def qI (a b c:zu):KD:=a 0*(b 1*c 2+b 2*c 1)+a 1*(b 0*c 2+b 2*c 0)+a 2*(b 0*c 1+b 1*c 0)
def zZ (a:Fin 4->KD) (h:Fin 4):zu:=fun k=>a (z8 h k)
abbrev qv (X:ze) (i:Fin 4):zu:=zZ (zI X i) 0
def jf (L:Submodule KD ze):Submodule KD ze:=zh L 0⊓LinearMap.ker (z9 1)⊓LinearMap.ker (z9 2)
def Ze (L:Submodule KD ze):Prop:=zg L/\finrank KD L=6/\finrank KD (L.map (z9 0))=3/\finrank KD ((zh L 0).map (z9 1))≤1/\finrank KD ((zh L 0).map (z9 2))≤1
def ZW (L:Submodule KD ze) (l:(Fin 4->KD)→ₗ[KD]KD):Prop:=Ze L/\∀a,∀T∈L,l (fun j=>a+T (0,j))=a
lemma kD:qk∈zP L:=mem_sup_right (mem_span_singleton_self _)
lemma wA (h:X∈L):X∈zP L:=mem_sup_left h
lemma yo {X T} (hX:X∈zP L) (hT:T∈L) (c:KD):X+c•T∈zP L:=add_mem hX ((zP L).smul_mem c (wA hT))
lemma Qn (hL:zg L) (h:X∈zP L):yM X X X X=24*y4 X^4:=by
 rw [<-yG hL h,zY];simp [zs,yM,je,zI];ring
lemma kE (hL:zg L) {X T} (hX:X∈zP L) (hT:T∈L) (h0:∀j,T (0,j)=0):yM X T X X+yM X X T X+yM X X X T=0/\yM X T T X+yM X T X T+yM X X T T=0/\yM X T T T=0:=by
 refine(qE 0 _ _ _ fun t=>?_).2
 have:=Qn hL (yo hX hT t);rw [map_add,map_smul,yf hL hT,smul_zero,add_zero,<-Qn hL hX] at this;simp [yM,je,zI,h0] at this ⊢;grind
lemma yP (h:ZW L l) (c:Fin 4->KD):∃X∈zP L,zI X 0=c/\y4 X=l c:=by
 have ⟨⟨hL,_,h3,_⟩,hl⟩:=h;obtain ⟨a,T,hT,rfl⟩:=(qu hL h3).1 c;refine ⟨T+a•qk,add_mem (wA hT) ((zP L).smul_mem a kD),funext fun j=>by simp [zI,qk,add_comm],?_⟩
 rw [map_add,map_smul,yf hL hT,jI,hl _ _ hT];simp
lemma ZX (h:Ze L):∃l,ZW L l:=let ⟨l,hl,_⟩:=(qu h.1 h.2.2.1).2;⟨l,h,hl⟩
lemma vR (h:ZW L l):∃j,l (single j 1)≠0:=by
 by_contra c;push Not at c;have:=h.2 1 0 L.zero_mem;rw [show (fun j:Fin 4=>(1:KD)+(0:ze) (0,j))=∑j,single j 1 by ext i;simp [Finset.sum_apply,Pi.single_apply],map_sum] at this;simp [c] at this
lemma wm (h:Fin 4) (a b c d:Fin 4->KD):je a b c d=a h*qI (zZ b h) (zZ c h) (zZ d h)+b h*qI (zZ a h) (zZ c h) (zZ d h)+c h*qI (zZ a h) (zZ b h) (zZ d h)+d h*qI (zZ a h) (zZ b h) (zZ c h):=by fin_cases h<;>simp [je,qI,zZ,z8]<;>ring
lemma xp (j:Fin 4) (a b c:Fin 4->KD):je (single j 1) a b c=qI (zZ a j) (zZ b j) (zZ c j):=by fin_cases j<;>simp [je,qI,zZ,z8]<;>ring
lemma Wl {E:Type} [AddCommGroup E] [Module KD E] [FiniteDimensional KD E] (S:Submodule KD E) (hS:finrank KD S≤1) {u v:E} (hu:u∈S) (h0:u≠0) (hv:v∈S):∃x:KD,v=x•u:=by
 have e:=eq_of_le_of_finrank_le ((span_singleton_le_iff_mem _ _).2 hu) (by rw [finrank_span_singleton h0];omega)
 have ⟨x,hx⟩:=mem_span_singleton.1 (e▸hv:v∈span KD {u});exact ⟨x,hx.symm⟩
lemma v9 {i X}:X∈LinearMap.ker (z9 i)↔∀j,X (i,j)=0:=by rw [LinearMap.mem_ker,funext_iff];rfl
lemma yt {X}:X∈jf L↔X∈L/\(∀j,X (0,j)=0)/\(∀j,X (1,j)=0)/\∀j,X (2,j)=0:=by simp only [jf,zh,mem_inf,v9,and_assoc]
lemma jL {X}:X∈zh L 0↔X∈L/\∀j,X (0,j)=0:=by simp only [zh,mem_inf,v9]
lemma wn (hL:zg L) (h:X∈L):∑i,∑j,X (i,j)=0:=by simpa [qY,Fintype.sum_prod_type] using (qb hL h).1
lemma YO (hL:zg L) (h6:finrank KD L=6) (hF:3≤finrank KD (jf L)):False:=by
 let H:=LinearMap.ker (∑j,LinearMap.proj (R:=KD) (φ:=fun _:Fin 4=>KD) j)
 have hle:(jf L).map (z9 3)≤H:=by
  rintro _ ⟨X,hX,rfl⟩;have ⟨XL,h0,h1,h2⟩:=yt.1 hX;have:=wn hL XL
  simp [Fin.sum_univ_four,h0,h1,h2] at this;simp [H,zA,Fin.sum_univ_four];grind
 have:=zW (z9 3) (jf L);rw [show jf L⊓LinearMap.ker (z9 3)=⊥ from eq_bot_iff.2 fun X hX=>by
  have ⟨hX1,hX2⟩:=mem_inf.1 hX;have ⟨_,h0,h1,h2⟩:=yt.1 hX1
  rw [mem_bot];funext ⟨i,j⟩;fin_cases i;exacts [h0 j,h1 j,h2 j,v9.1 hX2 j],finrank_bot,add_zero] at this
 have e:=eq_of_le_of_finrank_le hle ((wK _ fun h=>by simp [H] at h).trans (by omega))
 have:=wL hL 3 fun w hw=>by
  have h:w∈H:=by simp [H,hw]
  rw [<-e] at h;obtain ⟨X,hX,rfl⟩:=h;have ⟨XL,h0,h1,h2⟩:=yt.1 hX
  convert XL using 1;funext ⟨i,j⟩;fin_cases i<;>simp [h0,h1,h2,zA]
 omega
lemma xq {x:zu} (h:x≠0):x 0≠0\/x 1≠0\/x 2≠0:=by contrapose! h;funext i;fin_cases i<;>simp [h]
def yV (a:Fin 4->KD):KD:=a 0+a 1+a 2+a 3
def wu (a b:Fin 4->KD):KD:=a 0*b 0+a 1*b 1+a 2*b 2+a 3*b 3
def wB (L:Submodule KD ze) (l:(Fin 4->KD)→ₗ[KD]KD) (A B W:ze):Prop:=ZW L l/\(A∈L/\∀j,A (0,j)=0)/\(B∈L/\∀j,B (0,j)=0)/\(W∈L/\(∀j,W (0,j)=0)/\(∀j,W (1,j)=0)/\∀j,W (2,j)=0)/\(∀j,A (2,j)=0)/\(∀j,B (1,j)=0)/\zI A 1≠0/\zI B 2≠0/\zI W 3≠0/\∀T∈zh L 0,∃x y z:KD,T=x•A+y•B+z•W
lemma Zf (hS:ZW L l) (hF:finrank KD (jf L)=1) {W} (hW:W∈jf L) (hW0:W≠0):∃A B,wB L l A B W:=by
 have ⟨⟨_,h6,hr,h1,h2⟩,_⟩:=id hS;have hK:=y5 h6 hr;have hs:∀{X},X∈zh L 0->(∀j,X (1,j)=0)->(∀j,X (2,j)=0)->X∈jf L:=fun hX a b=>yt.2 ⟨(jL.1 hX).1,(jL.1 hX).2,a,b⟩
 have ex:∀i i':Fin 4,finrank KD ((zh L 0).map (z9 i'))≤1->(∀X∈zh L 0,(∀j,X (i,j)=0)->(∀j,X (i',j)=0)->X∈jf L)->∃A∈zh L 0,(∀j,A (i',j)=0)/\zI A i≠0:=by
  intro i i' hi hF';have:=zW (z9 i') (zh L 0);by_contra hc;push Not at hc
  have:=finrank_mono (show zh L 0⊓LinearMap.ker (z9 i')≤jf L from fun X hX=>hF' X hX.1 (congrFun (hc X hX.1 (v9.1 hX.2))) (v9.1 hX.2));omega
 have ⟨A,hA,hA2,hA1⟩:=ex 1 2 h2 fun X hX a b=>hs hX a b
 have ⟨B,hB,hB1,hB2⟩:=ex 2 1 h1 fun X hX a b=>hs hX b a
 have ⟨_,w0,w1,w2⟩:=yt.1 hW;refine ⟨A,B,hS,jL.1 hA,jL.1 hB,yt.1 hW,hA2,hB1,hA1,hB2,fun h=>hW0 (funext fun ⟨i,j⟩=>by fin_cases i;exacts [w0 j,w1 j,w2 j,congrFun h j]),fun T hT=>?_⟩
 have ⟨x,hx⟩:=Wl _ h1 (mem_map_of_mem hA) hA1 (mem_map_of_mem hT);have hT1:=sub_mem hT (smul_mem _ x hA);have ⟨y,hy⟩:=Wl _ h2 (mem_map_of_mem hB) hB2 (mem_map_of_mem hT1);have ⟨z,hz⟩:=Wl _ hF.le hW hW0 (hs (sub_mem hT1 (smul_mem _ y hB)) (fun j=>by have:=congrFun hx j;simp [zA] at this;simp [hB1 j,this]) fun j=>by have:=congrFun hy j;simp [zA,hA2] at this;simp [this,hA2])
 exact ⟨x,y,z,by rw [<-hz];abel⟩
lemma jg (Q:wB L l A B W) (hX:X∈zP L):yM X X X W=0/\yM X A X X+yM X X X A=0/\yM X A X A=0/\yM X X B X+yM X X X B=0/\yM X X B B=0/\yM X A B X+yM X A X B+yM X X B A=0:=by
 have ⟨⟨⟨hL,_⟩,_⟩,⟨AL,hA0⟩,⟨BL,hB0⟩,⟨WL,hW0,hW1,hW2⟩,hA2,hB1,_⟩:=Q;have a:=kE hL hX WL hW0;have b:=kE hL hX AL hA0;have c:=kE hL hX BL hB0;have d:=kE hL hX (add_mem AL BL) fun j=>by simp [hA0,hB0]
 simp only [yM,je,zI,Pi.add_apply,hW1,hW2,hA2,hB1] at a b c d ⊢;refine ⟨?_,?_,?_,?_,?_,?_⟩<;>grind
lemma wo (Q:wB L l A B W):(∀c,je c (zI A 1) (zI B 2) (zI W 3)=0/\je c (zI A 1) (zI B 2) (zI A 3)=0/\je c (zI A 1) (zI B 2) (zI B 3)=0)/\yV (zI W 3)=0/\wu (zI A 1) (zI W 3)=0/\wu (zI B 2) (zI W 3)=0/\yV (zI A 1)+yV (zI A 3)=0/\yV (zI B 2)+yV (zI B 3)=0/\yV (zI A 1)*yV (zI A 3)-wu (zI A 1) (zI A 3)=0/\yV (zI B 2)*yV (zI B 3)-wu (zI B 2) (zI B 3)=0:=by
 have ⟨hS,⟨AL,hA0⟩,⟨BL,hB0⟩,_,hA2,hB1,_⟩:=id Q;refine ⟨fun c=>?_,?_⟩
 . obtain ⟨X,hX,rfl,-⟩:=yP hS c
   have i:=jg Q hX;have j:=jg Q (yo hX AL 1);have k:=jg Q (yo hX BL 1);have m:=jg Q (yo (yo hX AL 1) BL 1)
   simp only [yM,je,zI,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hA0,hB0,hA2,hB1] at i j k m ⊢
   refine ⟨?_,?_,?_⟩<;>grind
 . have i:=jg Q kD;have j:=jg Q (yo kD AL 1);have k:=jg Q (yo kD BL 1)
   simp only [yM,je,zI,qk,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hA0,hB0,hA2,hB1,yV,wu] at i j k ⊢
   refine ⟨?_,?_,?_,?_,?_,?_,?_⟩<;>grind
lemma xr {w x:zu} (hw:∀k,w k≠0) (h:∀k,qI (single k 1) x w=0):x=0:=by
 have a:=h 0;have b:=h 1;have c:=h 2;have:=hw 0;have:=hw 1;have:=hw 2;simp [qI] at a b c;funext i;fin_cases i<;>simp<;>grind
lemma YP {w a1 a2 b1 b2:zu} (hw:∀k,w k≠0) (h:∀x y:KD,qI (a1+x•a2) (b1+y•b2) w=0) (ha:a2≠0) (ha':∀x:KD,a1+x•a2≠0) (hb:b2≠0) (hb':∀x:KD,b1+x•b2≠0):False:=by
 have I:∀{a b:zu},b≠0->(∀x:KD,a+x•b≠0)->LinearIndependent KD ![a,b]:=fun hb h=>LinearIndependent.pair_iff.2 fun s t e=>by
  by_cases hs:s=0
  . subst hs;simp at e;exact ⟨rfl,e.resolve_right hb⟩
  . exact (h (s⁻¹*t) (by simpa [smul_add,smul_smul,hs] using congrArg (s⁻¹•·) e)).elim
 have q:∀x y:KD,yH w (a1+x•a2) (b1+y•b2)=0:=fun x y=>by rw [<-h x y];simp [yH,qI];ring
 have e1:=q 0 0;have e2:=q 1 0;have e3:=q 0 1;have e4:=q 1 1;simp only [zero_smul,add_zero,one_smul,map_add,LinearMap.add_apply] at e1 e2 e3 e4;have f2:yH w a2 b1=0:=by grind
 have f3:yH w a1 b2=0:=by grind
 have f4:yH w a2 b2=0:=by grind
 have key:=qr (yH w) (span KD (Set.range ![a1,a2])) (span KD (Set.range ![b1,b2])) fun x hx y hy=>by
  obtain ⟨c,rfl⟩:=(mem_span_range_iff_exists_fun KD).1 hx;obtain ⟨d,rfl⟩:=(mem_span_range_iff_exists_fun KD).1 hy
  simp [Fin.sum_univ_two,e1,f2,f3,f4]
 rw [finrank_span_eq_card (I ha ha'),finrank_span_eq_card (I hb hb'),finrank_fin_fun,w7 _ fun x hx=>xr hw fun k=>by have:=hx (single k 1);simp [yH] at this;simp [qI];grind,inf_bot_eq,finrank_bot] at key;simp at key
lemma wY (hL:zg L) {X T} (hT:T∈L) (c:KD):y4 (X+c•T)=y4 X:=by rw [map_add,map_smul,yf hL hT,smul_zero,add_zero]
lemma ZY (b c:zu):qI 0 b c=0/\qI b 0 c=0:=by simp [qI]
lemma kF (hL:zg L) {X j} (hX:X∈zP L) (h0:zI X 0=single j 1) (ha:y4 X≠0):zZ (zI X 1) j≠0/\zZ (zI X 2) j≠0/\zZ (zI X 3) j≠0:=by
 have e:=Qn hL hX;simp only [yM,h0,xp] at e;refine ⟨fun h=>ha ?_,fun h=>ha ?_,fun h=>ha ?_⟩<;>simp [h,qI] at e<;>exact e
lemma xs:∀h j:Fin 4,j≠h->∃k,z8 h k=j:=by decide
lemma wp (h:Fin 4) (k:Fin 3):z8 h k≠h:=by fin_cases h<;>fin_cases k<;>decide
lemma wG (h:Fin 4) (k:Fin 3):zZ (single (z8 h k) 1) h=single k 1:=by funext m;fin_cases h<;>fin_cases k<;>fin_cases m<;>simp [zZ,z8]
lemma vS (h:Fin 4):zZ (single h 1) h=0:=by funext m;fin_cases h<;>fin_cases m<;>simp [zZ,z8]
lemma jW {a:Fin 4->KD} {h} (h2:zZ a h=0) (h1:a h=0):a=0:=by
 funext i;by_cases e:i=h
 . rw [e,h1];rfl
 obtain ⟨k,rfl⟩:=xs h i e;exact congrFun h2 k
lemma xt (h:Fin 4) (a:Fin 4->KD):yV a=a h+(zZ a h 0+zZ a h 1+zZ a h 2):=by fin_cases h<;>simp [yV,zZ,z8]<;>ring
lemma ve (h:Fin 4) (a b:Fin 4->KD):wu a b=a h*b h+(zZ a h 0*zZ b h 0+zZ a h 1*zZ b h 1+zZ a h 2*zZ b h 2):=by fin_cases h<;>simp [wu,zZ,z8]<;>ring
lemma Zg (Q:wB L l A B W) {j} (hj:l (single j 1)≠0) (hw:∀k,W (3,z8 j k)≠0) (hu:zZ (zI A 1) j≠0) (hv:zZ (zI B 2) j≠0):False:=by
 have ⟨X,hX,h0,ha⟩:=yP Q.1 (single j 1);have ⟨⟨⟨hL,_⟩,_⟩,⟨AL,hA0⟩,⟨BL,hB0⟩,_,hA2,hB1,_⟩:=id Q;have hα:∀{T},T∈L->∀x:KD,y4 (X+x•T)≠0:=fun hT x=>by rw [map_add,map_smul,yf hL hT,ha];simpa using hj
 have r:∀{T},T∈L->(∀j,T (0,j)=0)->∀x:KD,zI (X+x•T) 0=single j 1:=fun _ h x=>by rw [<-h0];funext k;simp [zI,h]
 refine YP (w:=zZ (zI W 3) j) hw (fun x y=>?_) hu (fun x e=>(kF hL (yo hX AL x) (r AL hA0 x) (hα AL x)).1 e) hv fun x e=>(kF hL (yo hX BL x) (r BL hB0 x) (hα BL x)).2.1 e
 have e:=(jg Q (yo (yo hX AL x) BL y)).1;rw [yM,show zI (X+x•A+y•B) 0=single j 1 by rw [<-h0];funext k;simp [zI,hA0,hB0],xp] at e
 convert e using 2<;>funext k<;>simp [zZ,zI,hA2,hB1]
lemma Jt (Q:wB L l A B W) (h4:∀j,W (3,j)≠0):False:=by
 have ⟨j,hj⟩:=vR Q.1;have ⟨_,_,u,v,_⟩:=wo Q;have ⟨_,_,_,_,_,_,hu,hv,_⟩:=id Q;refine Zg Q hj (fun _=>h4 _) (fun e=>hu (jW e ?_)) fun e=>hv (jW e ?_)
 . rw [ve j,e] at u;simpa [zI,h4 j] using u
 . rw [ve j,e] at v;simpa [zI,h4 j] using v
def qy:Prop:=∀(L:Submodule KD ze),zg L->finrank KD L=6-> y7∈L->(∀T∈L,∀k:Fin 3,T (1,k.succ)=T (2,k.succ))\/∃c:Fin 3,∀T∈L,T (1,c.succ)=T (2,c.succ)/\T (1,(z6 c 0).succ)-T (2,(z6 c 0).succ)=-(T (1,(z6 c 1).succ)-T (2,(z6 c 1).succ))
def yQ:Prop:=∀(L:Submodule KD ze),zg L->finrank KD L=6-> y7∈L->finrank KD (L.map (z9 0))=3->(¬∀T∈L,∀k:Fin 3,T (1,k.succ)=T (2,k.succ))->∃c:Fin 3,∀T∈L,T (1,c.succ)=T (2,c.succ)/\T (0,c.succ)=T (3,c.succ)/\T (0,(z6 c 0).succ)+T (3,(z6 c 0).succ)=T (0,(z6 c 1).succ)+T (3,(z6 c 1).succ)
def vT (r1 r2 h:Fin 4):ze:=fun x=>if x=(r1,h) then 1 else if x=(r2,h) then -1 else 0
lemma Ju:∀a b:Fin 4,a≠b->(swap ((swap 1 a) 2) b*swap 1 a) 1=a/\(swap ((swap 1 a) 2) b*swap 1 a) 2=b:=by decide
lemma Zh (F:qy) (hL:zg L) (h6:finrank KD L=6) {r1 r2 h:Fin 4} (hr:r1≠r2) (hE:vT r1 r2 h∈L):∃c,c≠h/\∀T∈L,T (r1,c)=T (r2,c):=by
 obtain ⟨p,rfl,rfl⟩:∃p:Perm (Fin 4),p 1=r1/\p 2=r2:=⟨_,Ju r1 r2 hr⟩;obtain ⟨q,rfl⟩:∃q:Perm (Fin 4),q 0=h:=⟨_,Equiv.swap_apply_left 0 h⟩;have hA:y7∈L.map (zq p q).toLinearMap:=⟨_,hE,funext fun ⟨i,j⟩=>by simp [zy,vT,y7]⟩
 have ⟨k,hk⟩:∃k:Fin 3,∀T∈L.map (zq p q).toLinearMap,T (1,k.succ)=T (2,k.succ):=(F _ (zH hL p q) (by rw [zF];exact h6) hA).elim (fun h=>⟨0,fun T hT=>h T hT 0⟩) fun ⟨c,h⟩=>⟨c,fun T hT=>(h T hT).1⟩
 exact ⟨q k.succ,fun e=>Fin.succ_ne_zero k (q.injective e),fun T hT=>hk _ (mem_map_of_mem hT)⟩
lemma Zi (F:qy) (hL:zg L) (h6:finrank KD L=6) {r a b:Fin 4} (hab:a≠b) (hE:(fun x:Fin 4×Fin 4=>vT a b r (x.2,x.1))∈L):∃i,i≠r/\∀T∈L,T (i,a)=T (i,b):=by
 have ⟨c,hc,h⟩:=Zh F (zX hL) (by rw [zT];exact h6) hab ⟨_,hE,funext fun _=>rfl⟩
 exact ⟨c,hc,fun T hT=>h _ ⟨T,hT,rfl⟩⟩
lemma wH {U1 U2 W1 W2:KD} (b1 b2:KD) (hU:U1≠0\/U2≠0) (hW:W1≠0\/W2≠0) (h1:U1*W2+U2*W1=0) (h2:U1*b2+U2*b1=0):∃y,b1+y*W1=0/\b2+y*W2=0:=by
 rcases hU with h|h
 . have:W1≠0:=by grind
   exact ⟨-b1/W1,by grind⟩
 . have:W2≠0:=by grind
   exact ⟨-b2/W2,by grind⟩
lemma Jv (k:Fin 3) (y z:zu):qI (single k 1) y z=y (z6 k 0)*z (z6 k 1)+y (z6 k 1)*z (z6 k 0):=by fin_cases k<;>simp [qI,z6]
lemma YQ {k:Fin 3} {U V W P Q a b d:zu} {β1 β2 β3 c:KD} (hc:c≠0) (hU:U (z6 k 0)≠0\/U (z6 k 1)≠0) (hV:V (z6 k 0)≠0\/V (z6 k 1)≠0) (hW1:W (z6 k 0)≠0) (hW2:W (z6 k 1)≠0) (h:∀x y z:KD,β1*qI (single k 1) (b+y•V) (d+x•P+y•Q+z•W)+β2*qI (single k 1) (a+x•U) (d+x•P+y•Q+z•W)+β3*qI (single k 1) (a+x•U) (b+y•V)=c):False:=by
 simp [Jv] at h;generalize z6 k 0=s at *;generalize z6 k 1=t at *;have h0:=h 0 0 0;have hz:=h 0 0 1;have hxz:=h 1 0 1;have hx:=h 1 0 0;have hx':=h (-1) 0 0;have hy:=h 0 1 0;have hy':=h 0 (-1) 0;have hyz:=h 0 1 1;have hxy:=h 1 1 0;have hW:W s≠0\/W t≠0:=Or.inl hW1;by_cases e1:β1=0<;>by_cases e2:β2=0
 . have ⟨y,e,f⟩:=wH (b s) (b t) hU hV (by grind) (by grind);have:=h 0 y 0;grind
 . have ⟨x,e,f⟩:=wH (a s) (a t) hW hU (by grind) (by grind);have:=h x 0 0;grind
 . have ⟨y,e,f⟩:=wH (b s) (b t) hW hV (by grind) (by grind);have:=h 0 y 0;grind
 have ⟨ρ,r1,r2⟩:=wH (P s) (P t) hU hW (by grind) (by grind)
 have ⟨σ,s1,s2⟩:=wH (Q s) (Q t) hV hW (by grind) (by grind)
 have:U s≠0:=by grind
 have:V s≠0:=by grind
 have:β3=0:=by grind
 have ⟨κ,k1,k2⟩:=wH (d s) (d t) hU hW (by grind) (by grind)
 grind
lemma Jw {u v w:zu} (hw:∀k,w k≠0) (hu:u≠0) (hv:v≠0) (a:u 0*w 0+u 1*w 1+u 2*w 2=0) (b:v 0*w 0+v 1*w 1+v 2*w 2=0) (c:∀k,qI (single k 1) u v=0):False:=by
 have:=c 0;have:=c 1;have:=c 2;have:=hw 0;have:=hw 1;have:=hw 2;have:=xq hu;have:=xq hv;simp [qI] at *;grind
lemma Jx {w a:zu} (hw:∀k,w k≠0) (hs:w 0+w 1+w 2=0) (hd:a 0*w 0+a 1*w 1+a 2*w 2=0) (hp:qI a a w=0):a 1=a 0/\a 2=a 0:=by have:=hw 0;have:=hw 1;have:=hw 2;simp [qI] at hp;grind
lemma Jy {a w:zu} (k:Fin 3) (hw:∀k,w k≠0) (ha:a≠0) (hd:a 0*w 0+a 1*w 1+a 2*w 2=0):a (z6 k 0)≠0\/a (z6 k 1)≠0:=by
 have:=xq ha;have:=hw 0;have:=hw 1;have:=hw 2;fin_cases k<;>simp [z6] at *<;>grind
lemma kn {z:zu} {D:Fin 3->zu} {c:KD} (hs:z 0+z 1+z 2=0) (hD:∀i,∑j,D i j=c) (hQ:∀x:zu,qI x (fun i=>∑j,D i j*x j) z=0) (a:Fin 3):∑i,D i a*z i=-c*z a:=by
 have:=hQ (single 0 1);have:=hQ (single 1 1);have:=hQ (single 2 1);have:=hQ (single 0 1+single 1 1);have:=hQ (single 0 1+single 2 1);have:=hQ (single 1 1+single 2 1);have:=hD 0;have:=hD 1;have:=hD 2;simp [qI,Fin.sum_univ_three,Pi.single_apply] at *;fin_cases a<;>simp<;>grind
lemma Jz {w p:zu} {D:Fin 3->zu} (hw:∀k,w k≠0) (hsw:w 0+w 1+w 2=0) (hsp:p 0+p 1+p 2=0) (hδ:p 0*w 1-p 1*w 0≠0) (hD:∀i,∑j,D i j=1) (hQ:∀x:zu,qI x (fun i=>∑j,D i j*x j) w=0) (hp:∀a,∑i,D i a*p i=-1*p a):False:=by
 have:=kn hsw hD hQ 0;have:=kn hsw hD hQ 1;have:=kn hsw hD hQ 2;have:=hp 0;have:=hp 1;have:=hp 2;have:=hw 0;have:=hw 1;have:=hw 2;have:=hQ (single 0 1);have:=hQ (single 1 1);have:=hQ (single 2 1);have:=hQ (single 0 1+single 1 1);have:=hQ (single 0 1+single 2 1);have:=hQ (single 1 1+single 2 1);have:=hD 0;have:=hD 1;have:=hD 2;simp [qI,Fin.sum_univ_three,Pi.single_apply] at *;grind
lemma kU:∀h:Fin 4,∀a b:Fin 3,z8 h a=z8 h b↔a=b:=by decide
lemma JA (X Y:ze) (i:Fin 4):zI (X+Y) i=zI X i+zI Y i:=rfl
lemma JB (a b:Fin 4->KD) (h:Fin 4):zZ (a+b) h=zZ a h+zZ b h:=rfl
lemma YR (a b b' c:zu):qI a (b+b') c=qI a b c+qI a b' c:=by simp only [qI,Pi.add_apply];ring
lemma JC (Q:wB L l A B W) {h} (hwh:W (3,h)=0) (hwI:∀k,zZ (zI W 3) h k≠0) (huh:A (1,h)=0) (hvh:B (2,h)=0):False:=by
 have ⟨hF,_,huw,hvw,_⟩:=wo Q;have ⟨hS,⟨AL,hA0⟩,⟨BL,hB0⟩,⟨WL,hW0,hW1,hW2⟩,hA2,hB1,hu,hv,_⟩:=id Q;have ⟨⟨hL,_⟩,_⟩:=id hS;have huI:zZ (zI A 1) h≠0:=fun e=>hu (jW e huh)
 have hvI:zZ (zI B 2) h≠0:=fun e=>hv (jW e hvh)
 rw [ve h,show zI A 1 h=0 from huh,zero_mul,zero_add] at huw;rw [ve h,show zI B 2 h=0 from hvh,zero_mul,zero_add] at hvw;have ⟨k0,hk0⟩:∃k,qI (single k 1) (zZ (zI A 1) h) (zZ (zI B 2) h)≠0:=by by_contra c;push Not at c;exact Jw hwI huI hvI huw hvw c
 have ex:∀r:ze,je (single (z8 h k0) 1) (zI A 1) (zI B 2) (zI r 3)=0-> r (3,h)=0:=fun r e=>by
  rw [wm h,Pi.single_eq_of_ne (wp h k0).symm,wG,show zI A 1 h=0 from huh,show zI B 2 h=0 from hvh] at e;simp at e;exact e.resolve_right hk0
 have hph:=ex A (hF _).2.1;have hqh:=ex B (hF _).2.2;have ⟨j,hj⟩:=vR hS;by_cases e:j=h
 . subst e;exact Zg Q hj hwI huI hvI
 obtain ⟨k,rfl⟩:=xs h j e;have ⟨X,hX,h0,ha⟩:=yP hS (single (z8 h k) 1);refine YQ (k:=k) (W:=zZ (zI W 3) h) (P:=zZ (zI A 3) h) (Q:=zZ (zI B 3) h) (a:=zZ (zI X 1) h) (b:=zZ (zI X 2) h) (d:=zZ (zI X 3) h) (β1:=X (1,h)) (β2:=X (2,h)) (β3:=X (3,h)) (c:=24*y4 X^4) (by simp [ha,hj]) (Jy k hwI huI huw) (Jy k hwI hvI hvw) (hwI _) (hwI _) fun x y z=>?_
 have e:=Qn hL (yo (yo (yo hX AL x) BL y) WL z);rw [wY hL WL,wY hL BL,wY hL AL,yM,wm h,show zI (X+x•A+y•B+z•W) 0=single (z8 h k) 1 by rw [<-h0];funext j;simp [zI,hA0,hB0,hW0],Pi.single_eq_of_ne (wp h k).symm,wG] at e
 rw [<-e];simp only [qI,zZ,zI,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hA2,hB1,hW1,hW2,huh,hvh,hwh,hph,hqh];ring
lemma JD (Q:wB L l A B W) {h} (hwh:W (3,h)=0) (hwI:∀k,zZ (zI W 3) h k≠0) (hvh:B (2,h)≠0) (huI:zZ (zI A 1) h≠0) (rel:∀k,A (1,h)*zZ (zI B 2) h k+B (2,h)*zZ (zI A 1) h k=0):False:=by
 have ⟨hF,hsw,huw,_,hup,hvq,_⟩:=wo Q;have e:=hF (single h 1);have f:=hF (single (z8 h 0) 1);simp only [wm h,Pi.single_eq_same,vS,Pi.single_eq_of_ne (wp h 0).symm,wG,ZY,ve h,xt h,show zI W 3 h=0 from hwh,zero_mul,mul_zero,add_zero,zero_add,one_mul] at e f huw hsw hup hvq;have r0:=rel 0;have r1:=rel 1;have r2:=rel 2;have r:=Jx hwI hsw huw (by simp [qI] at e ⊢;grind)
 have ⟨_,e1,e2⟩:=e;have ⟨_,f1,f2⟩:=f;have hz:=xq huI;clear hF Q rel huw hsw hwI huI;simp [qI,zZ,zI] at *;generalize z8 h=s at *;simp only [r.1,r.2] at *;have hU:A (1,h)≠0:=fun e=>by simp [e,hvh] at r0;simp [r0] at hz
 have b1:B (2,s 1)=B (2,s 0):=by grind
 have b2:B (2,s 2)=B (2,s 0):=by grind
 simp only [b1,b2] at *;have:12*(A (1,s 0)*B (2,s 0))^2=0:=by linear_combination 2*A (1,s 0)*B (2,s 0)*(B (2,s 0)*hup+A (1,s 0)*hvq-r0)-B (2,s 0)*(f1-(A (3,s 1)+A (3,s 2))*r0)-B (2,s 0)*e1-A (1,s 0)*(f2-(B (3,s 1)+B (3,s 2))*r0)-A (1,s 0)*e2
 simp at this;rcases this with e|e;simp [e] at hz;simp [e,hvh] at r0;simp [r0] at hz
lemma JE (F:qy) (Q:wB L l A B W) {h} (hwh:W (3,h)=0) (hwI:∀k,zZ (zI W 3) h k≠0) (huI:zZ (zI A 1) h=0) (hvI:zZ (zI B 2) h=0):False:=by
 have ⟨_,hsw,_,_,hup,_,hbp,_⟩:=wo Q;have ⟨hS,⟨AL,hA0⟩,_,⟨WL,hW0,hW1,hW2⟩,hA2,hB1,hu,_,_,hsp⟩:=id Q;have ⟨⟨hL,h6,_⟩,_⟩:=id hS;have huh:zI A 1 h≠0:=fun e=>hu (jW huI e)
 simp only [xt h,ve h,huI,show zI W 3 h=0 from hwh,Pi.zero_apply,zero_mul,add_zero,zero_add] at hsw hup hbp;have hsI:zZ (zI A 3) h 0+zZ (zI A 3) h 1+zZ (zI A 3) h 2=0:=by grind
 by_cases hδ:zZ (zI A 3) h 0*zZ (zI W 3) h 1-zZ (zI A 3) h 1*zZ (zI W 3) h 0=0
 . have m:=fun k=>congrFun huI k
   simp only [zZ,zI] at hsw hup hsI hδ m huh hwI
   have ⟨c,hc,hT⟩:=Zh F hL h6 (r1:=1) (r2:=3) (h:=h) (by decide) (by
    convert L.smul_mem (A (1,h))⁻¹ (sub_mem AL (L.smul_mem (A (3,z8 h 0)/W (3,z8 h 0)) WL)) using 1
    funext ⟨i,j⟩;by_cases e:j=h
    . subst e;fin_cases i<;>simp [vT,hA0,hW0,hW1,hW2,hA2,hwh,huh];grind
    . obtain ⟨k,rfl⟩:=xs h j e;have:=m k;fin_cases i<;>simp [vT,hA0,hW0,hW1,hW2,hA2,e] at *<;>fin_cases k<;>grind)
   obtain ⟨k,rfl⟩:=xs h c hc;exact hwI k (by rw [<-hT W WL,hW1])
 choose M MV hM0 _ using fun m:Fin 4=>yP hS (single m 1)
 have m0:∀m j,M m (0,j)=(single m 1:Fin 4->KD) j:=fun m j=>congrFun (hM0 m) j
 have T:∀X∈zP L,qI (zZ (zI X 0) h) (zZ (zI X 2) h) (zZ (zI W 3) h)=0/\qI (zZ (zI X 0) h) (zZ (zI X 2) h) (zZ (zI A 3) h)=0:=fun X hX=>by
  have i:=jg Q hX;have j:=(jg Q (yo hX AL 1)).1
  have e:je (zI X 0) (zI A 1) (zI X 2) (zI W 3)=0:=by have:=i.1;simp [yM,je,zI,hA0,hA2] at this j ⊢;grind
  have f:=i.2.2.1;rw [yM] at f
  simp only [wm h,huI,show zI W 3 h=0 from hwh,ZY,mul_zero,add_zero,zero_add] at e f
  grind
 have d0:∀x:zu,zZ (zI (∑k,x k•M (z8 h k)) 0) h=x:=fun x=>by funext i;simp [zI,zZ,Finset.sum_apply,m0,Pi.single_apply,kU]
 have d2:∀x:zu,zZ (zI (∑k,x k•M (z8 h k)) 2) h=fun i=>∑j,M (z8 h j) (2,z8 h i)*x j:=fun x=>by funext i;simp [zI,zZ,Finset.sum_apply,mul_comm]
 have V:∀x:zu,∑k,x k•M (z8 h k)∈zP L:=fun x=>sum_mem fun k _=>(zP L).smul_mem _ (MV _)
 have Q1:=fun x=>(T _ (V x)).1;have Q2:=fun x=>(T _ (V x)).2;simp only [d0,d2] at Q1 Q2
 have hβ:zZ (zI (M h) 2) h=0:=xr hwI fun k=>by
  have e1:=(T _ (add_mem (MV h) (MV (z8 h k)))).1;have e2:=(T _ (MV (z8 h k))).1
  rw [JA,JA,JB,JB,hM0,hM0,vS,wG,zero_add,YR] at e1;rw [hM0,wG] at e2;grind
 have hJ:qk-∑m,M m∈zh L 0:=by
  have z:∀j,(qk-∑m,M m) (0,j)=0:=fun j=>by simp [qk,Finset.sum_apply,m0,Pi.single_apply]
  exact jL.2 ⟨jQ hL (sub_mem kD (sum_mem fun m _=>MV m)) z,z⟩
 have ⟨a,b,c,habc⟩:=hsp _ hJ;have hD:∀i,∑j,M (z8 h j) (2,z8 h i)=1:=fun i=>by
  have e:=congrFun habc (2,z8 h i);have es:=xt h (fun m=>M m (2,z8 h i))
  have eb:B (2,z8 h i)=0:=congrFun hvI i;have em:M h (2,z8 h i)=0:=congrFun hβ i
  simp [qk,hA2,hW2,eb,Fin.sum_univ_four,Fin.sum_univ_three] at e ⊢;simp [yV,zZ,em] at es;grind
 exact Jz hwI hsw hsI hδ hD Q1 (kn hsI hD Q2)
lemma YS (F:qy) (Q:wB L l A B W) {h} (hwh:W (3,h)=0) (hwI:∀k,zZ (zI W 3) h k≠0):False:=by
 have ⟨hF,_⟩:=wo Q;have ⟨_,_,_,_,_,_,hu,hv,_⟩:=id Q;have z:=xr hwI (x:=A (1,h)•zZ (zI B 2) h+B (2,h)•zZ (zI A 1) h) fun k=>by
  have e:=(hF (single (z8 h k) 1)).1;rw [wm h,Pi.single_eq_of_ne (wp h k).symm,wG,show zI W 3 h=0 from hwh] at e
  simp [qI,zI] at e ⊢;grind
 have rel:∀k,A (1,h)*zZ (zI B 2) h k+B (2,h)*zZ (zI A 1) h k=0:=fun k=>by simpa using congrFun z k
 by_cases a:A (1,h)=0<;>by_cases b:B (2,h)=0
 . exact JC Q hwh hwI a b
 . exact hu (jW (funext fun k=>by simpa [a,b] using rel k) a)
 . exact hv (jW (funext fun k=>by simpa [a,b] using rel k) b)
 by_cases c:zZ (zI A 1) h=0
 . exact JE F Q hwh hwI c (funext fun k=>by simpa [c,a] using rel k)
 . exact JD Q hwh hwI b c rel
lemma kG {X Y} (hX:X∈zP L) (hY:Y∈zP L) (c:KD):X+c•Y∈zP L:=add_mem hX ((zP L).smul_mem c hY)
lemma xu {x:Fin 4->KD} (h:x≠0):x 0≠0\/x 1≠0\/x 2≠0\/x 3≠0:=by contrapose! h;funext i;fin_cases i<;>simp [h]
lemma Zj (a b c d:Fin 4->KD):je a b c d=je a c b d:=by simp only [je];ring
lemma Zk {u v p q:Fin 4->KD} (hM:∀j,je (single j 1) u v p=0/\je (single j 1) u v q=0) (h2:u 2=0) (h3:u 3=0) (h1:u 1=u 0) (k1:v 1=v 0) (h0:u 0≠0) (hv:v≠0) (s1:yV u+yV p=0) (b1:yV u*yV p-wu u p=0) (s2:yV v+yV q=0) (b2:yV v*yV q-wu v q=0):False:=by
 have ⟨e0,f0⟩:=hM 0;have ⟨e2,f2⟩:=hM 2;have ⟨e3,f3⟩:=hM 3;have:=xu hv;simp [je,yV,wu,h2,h3,h1,k1] at e0 f0 e2 f2 e3 f3 s1 b1 s2 b2 this;rcases eq_or_ne (v 2) 0 with h|h<;>grind
lemma JF {u v p:Fin 4->KD} (hM:∀j,je (single j 1) u v p=0) (h1:u 1=u 0) (h3:u 3=-u 2) (k1:v 1=v 0) (k3:v 3=v 2) (hb:u 2≠0) (hd:v 2≠0) (s1:yV u+yV p=0) (b1:yV u*yV p-wu u p=0):u 0=0/\p 3=p 2/\p 0+p 1+p 2+p 3=0:=by
 have m0:=hM 0;have m2:=hM 2;have m3:=hM 3;simp [je,yV,wu,h1,h3,k1,k3] at m0 m2 m3 s1 b1;rcases eq_or_ne (u 0) 0 with h|h;· grind
 rcases eq_or_ne (v 0) 0 with h'|h'<;>rcases eq_or_ne (u 0*v 2-u 2*v 0) 0 with h1|h1<;>rcases eq_or_ne (u 0*v 2+u 2*v 0) 0 with h2|h2<;>grind
lemma JG (hL:zg L) (hX:X∈zP L) (h:y4 X=0):X∈L:=by
 obtain ⟨T,hT,_,hc,rfl⟩:=mem_sup.1 hX;obtain ⟨c,rfl⟩:=mem_span_singleton.1 hc;rw [map_add,map_smul,yf hL hT,jI] at h;simp at h;simpa [h] using hT
lemma JH (hL:zg L) {N} (hN:N∈L) (a:∀j,N (0,j)=![1,-1,0,0] j) (e:N (1,0)-N (1,1)=-2) (f:N (1,2)=0) (g:N (1,3)=0) (k:∀j,N (2,j)=0) (m:N (3,0)=0) (n:N (3,1)=0) (o:N (3,2)=N (3,3)):False:=by
 have e1:=qP hL hN 1;have e2:=qP hL (L.neg_mem hN) 1;have e3:=qP hL (L.smul_mem 2 hN) 1;rw [zY] at e1 e2 e3;simp [zs,a,f,g,k,m,n,o] at e1 e2 e3;grind
lemma kH (hL:zg L) (hr:finrank KD (L.map (z9 0))=3) {a b:Fin 4} (hab:a≠b) (h:∀T∈L,T (0,a)=T (0,b)):False:=by
 have ⟨c,T,hT,e⟩:=(qu hL hr).1 (single a 1);have x:=congrFun e a;have y:=congrFun e b;simp [Ne.symm hab] at x y;have:=h T hT;grind
lemma JI (Q:wB L l A B W) (hw:zI W 3=![1,-1,0,0]) (hrow:∀T∈L,T (2,0)=T (2,1)):False:=by
 have ⟨hF,_,_,_,hup,hvq,hbp,hbq⟩:=wo Q;have ⟨hS,⟨AL,hA0⟩,⟨BL,hB0⟩,⟨WL,hW0,hW1,hW2⟩,hA2,hB1,hu,hv,_⟩:=id Q;have ⟨⟨hL,_⟩,hl⟩:=id hS;have wj:∀j,W (3,j)=![1,-1,0,0] j:=fun j=>congrFun hw j
 have dL:∀T∈L,T (0,0)-T (0,1)+(T (1,0)-T (1,1))+(T (2,0)-T (2,1))=0:=fun T hT=>by
  have a:=(qb hL (add_mem hT WL)).2.1;have b:=(qb hL hT).2.1
  simp [yl,Fintype.sum_prod_type,Fin.sum_univ_four,hW0,hW1,hW2,wj] at a b;grind
 have dV:∀X∈zP L,X (1,0)-X (1,1)=-(X (0,0)-X (0,1))/\X (2,0)=X (2,1):=fun X hX=>by
  obtain ⟨T,hT,_,hc,rfl⟩:=mem_sup.1 hX;obtain ⟨c,rfl⟩:=mem_span_singleton.1 hc
  have:=dL T hT;have:=hrow T hT;simp [qk];grind
 have u01:A (1,1)=A (1,0):=by have:=dL A AL;simp [hA0,hA2] at this;grind
 have v01:=(hrow B BL).symm;have ut:¬(A (1,2)=0/\A (1,3)=0):=fun ⟨a,b⟩=>Zk (fun _=>(hF _).2) a b u01 v01 (fun h=>hu (funext fun j=>by simp only [zI] at h ⊢;fin_cases j<;>simp [h,u01,a,b])) hv hup hbp hvq hbq
 have vt:¬(B (2,2)=0/\B (2,3)=0):=fun ⟨a,b⟩=>Zk (fun j=>⟨by rw [Zj];exact (hF _).2.2,by rw [Zj];exact (hF _).2.1⟩) a b v01 u01 (fun h=>hv (funext fun j=>by simp only [zI] at h ⊢;fin_cases j<;>simp [h,v01,a,b])) hu hvq hbq hup hbp
 have ⟨M,hM0,m0,ha0⟩:=yP hS (single 0 1);have m:=congrFun m0;simp [zI,Pi.single_apply] at m;have G:∀X∈zP L,(X (1,2)-X (0,2))*X (2,3)+(X (1,3)-X (0,3))*X (2,2)=0:=fun X hX=>by
  have k:∀t:KD,(X (0,0)-X (0,1)+t)*((X (1,2)+t*M (1,2)-X (0,2))*(X (2,3)+t*M (2,3))+(X (1,3)+t*M (1,3)-X (0,3))*(X (2,2)+t*M (2,2)))=0:=fun t=>by
   have Y:=kG hX hM0 t;have e:=(jg Q Y).1;have d:=dV _ Y;simp [yM,je,zI,wj,m] at e d;grind
  by_cases s:X (0,0)-X (0,1)=0
  . have a:=k 1;have b:=k (-1);have c:=k 2;rw [s] at a b c;grind
  . have:=k 0;simp at this;grind
 have GA:∀X∈zP L,A (1,2)*X (2,3)+A (1,3)*X (2,2)=0:=fun X hX=>by have a:=G X hX;have b:=G _ (yo hX AL 1);simp [hA0,hA2] at b;grind
 have GB:∀X∈zP L,(X (1,2)-X (0,2))*B (2,3)+(X (1,3)-X (0,3))*B (2,2)=0:=fun X hX=>by have a:=G X hX;have b:=G _ (yo hX BL 1);simp [hB0,hB1] at b;grind
 have u3:A (1,3)=-A (1,2):=by have:=GA _ kD;simp [qk] at this;grind
 have u2:A (1,2)≠0:=fun h=>ut ⟨h,by rw [u3,h,neg_zero]⟩
 have X23:∀X∈zP L,X (2,3)=X (2,2):=fun X hX=>by have:=GA X hX;grind
 have v3:=X23 B (wA BL);have v2:B (2,2)≠0:=fun h=>vt ⟨h,by rw [v3,h]⟩
 have X1t:∀X∈zP L,X (1,2)-X (0,2)+(X (1,3)-X (0,3))=0:=fun X hX=>by have:=GB X hX;grind
 have R2:∀T∈L,T (2,0)*B (2,2)=T (2,2)*B (2,0):=fun T hT=>by
  by_contra hne;apply qg hL 2;have t1:=hrow T hT;have t3:=X23 T (wA hT);have:T (2,0)*B (2,2)-T (2,2)*B (2,0)≠0:=sub_ne_zero.2 hne
  refine ⟨((B (2,2)-B (2,0))/(T (2,0)*B (2,2)-T (2,2)*B (2,0)))•T+((T (2,0)-T (2,2))/(T (2,0)*B (2,2)-T (2,2)*B (2,0)))•B,add_mem (L.smul_mem _ hT) (L.smul_mem _ BL),funext fun j=>?_⟩
  fin_cases j<;>simp [zA,<-t1,t3,v01,v3]<;>grind
 have ⟨a0,p32,sp⟩:=JF (fun _=>(hF _).2.1) u01 u3 v01 v3 u2 v2 hup hbp;simp only [zI] at a0 p32 sp
 have inact:∀j:Fin 4,j=0\/j=1->l (single j 1)=0:=fun j hj=>by
  by_contra hla;have ⟨X,hX,x0,ha⟩:=yP hS (single j 1);have t1:=X1t X hX;have t2:=X23 X hX
  have x2:X (0,2)=0:=by have:=congrFun x0 2;rcases hj with rfl|rfl<;>simpa [zI] using this
  have x3:X (0,3)=0:=by have:=congrFun x0 3;rcases hj with rfl|rfl<;>simpa [zI] using this
  have e:=Qn hL (yo (yo hX AL (-(X (1,2)/A (1,2)))) BL (-(X (2,2)/B (2,2))));rw [wY hL BL,wY hL AL,ha] at e
  simp [yM,je,zI,hA0,hB0,hA2,hB1,x2,x3,u3,v3,t2,u2,v2,show X (1,3)=-X (1,2) by grind,hla] at e
 have ⟨M2,hM2,m2,_⟩:=yP hS (single 2 1);have k:∀ε:KD,A (1,2)*(1+ε*M2 (2,0))*ε*(A (3,0)+A (3,1))=0:=fun ε=>by
  have e:=(jg Q (kG kD hM2 ε)).2.2.1;have z:=congrFun m2;have r1:=(dV M2 hM2).2.symm;have r3:=X23 M2 hM2
  simp [zI] at z;simp [yM,je,zI,qk,z,a0,u01,u3,p32,r1,r3] at e;grind
 have S0:A (3,0)+A (3,1)=0:=by have:=k 1;have:=k (-1);grind
 have p2z:A (3,2)=0:=by grind
 have p3z:A (3,3)=0:=by rw [p32,p2z]
 have hA':A-A (3,0)•W∈L:=sub_mem AL (L.smul_mem _ WL);have Phi0:∀X∈zP L,X (2,0)*((X (0,3)-X (0,2))*(X (3,0)+X (3,1))+(X (3,3)-X (3,2))*(X (0,0)+X (0,1)))=0:=fun X hX=>by
  have e:=(kE hL hX hA' fun j=>by simp [hA0,hW0]).1;have r1:=(dV X hX).2.symm;have r3:=X23 X hX
  simp [yM,je,zI,hA2,hW1,hW2,wj,a0,u01,u3,r1,r3,p2z,p3z,show A (3,1)=-A (3,0) by grind] at e;grind
 have Phi:∀X∈zP L,(X (0,3)-X (0,2))*(X (3,0)+X (3,1))+(X (3,3)-X (3,2))*(X (0,0)+X (0,1))=0:=fun X hX=>by
  have a:=Phi0 X hX;have b:=Phi0 _ (kG hX kD 1);have c:=Phi0 _ (kG hX kD (-1));simp [qk] at b c;grind
 have ⟨M1,hM1,m1,ha1⟩:=yP hS (single 1 1);have hN:M-M1∈L:=JG hL (sub_mem hM0 hM1) (by rw [map_sub,ha0,ha1,inact 0 (by simp),inact 1 (by simp),sub_zero])
 have z1:=congrFun m1;have z2:=congrFun m2;simp [zI,Pi.single_apply] at z1 z2;set N:=M-M1;have n0:N (0,0)=1/\N (0,1)=-1/\N (0,2)=0/\N (0,3)=0:=by simp [N,m,z1]
 set N1:=N-(N (1,2)/A (1,2))•(A-A (3,0)•W)-(N (2,2)/B (2,2))•B;have hN1:N1∈L:=sub_mem (sub_mem hN (L.smul_mem _ hA')) (L.smul_mem _ BL);have q01:N1 (3,0)+N1 (3,1)=0:=by have a:=Phi _ (kG (wA hN1) hM2 1);have b:=Phi _ hM2;simp [N1,N,m,z1,z2,hA0,hW0,hB0,wj] at a b ⊢;grind
 have q23:N1 (3,2)=N1 (3,3):=by have a:=Phi _ (kG (wA hN1) hM0 1);have b:=Phi _ hM0;simp [N1,N,m,z1,hA0,hW0,hB0,wj] at a b ⊢;grind
 have nr1:=(dV _ (wA hN)).1;have nt:=X1t _ (wA hN);have n23:=X23 _ (wA hN);have n21:=(dV _ (wA hN)).2;have nR:=R2 _ hN;have R:∀j,N (2,j)*B (2,2)=N (2,2)*B (2,j):=fun j=>by fin_cases j<;>simp [<-n21,n23,v01,v3,nR]
 refine JH hL (sub_mem hN1 (L.smul_mem (N1 (3,0)) WL)) (fun j=>by fin_cases j<;>simp [N1,n0,hA0,hB0,hW0]) ?_ ?_ ?_ (fun j=>?_) ?_ ?_ ?_
 . simp [N1,hW1,hB1,a0,u01];grind
 . simp [N1,hW1,hB1,u2]
 . simp [N1,hW1,hB1,u3,u2];grind
 . simp [N1,hA2,hW2];field_simp;grind
 . simp [wj]
 . simp [wj];grind
 . simp [wj,q23]
lemma JJ:∀a b:Fin 4,a≠b->(swap ((swap 0 a) 1) b*swap 0 a) 0=a/\(swap ((swap 0 a) 1) b*swap 0 a) 1=b:=by decide
theorem yN (S:Submodule KD ze) (p q:Perm (Fin 4)) (i:Fin 4):finrank KD ((S.map (zq p q:ze→ₗ[KD]ze)).map (z9 i))=finrank KD (S.map (z9 (p i))):=by
 rw [<-Submodule.map_comp,show z9 i∘ₗ(zq p q).toLinearMap=(LinearEquiv.funCongrLeft KD KD q:(Fin 4->KD)→ₗ[KD]_)∘ₗz9 (p i) by ext X j;rfl,Submodule.map_comp];exact LinearEquiv.finrank_map_eq _ _
lemma wI {S:Submodule KD ze} {p q:Perm (Fin 4)} {i i'} (h:p i=i'):S.map (zq p q).toLinearMap⊓LinearMap.ker (z9 i)=(S⊓LinearMap.ker (z9 i')).map (zq p q).toLinearMap:=by
 ext X;simp only [mem_inf,v9,mem_map];constructor
 . rintro ⟨⟨Y,hY,rfl⟩,e⟩;exact ⟨Y,⟨hY,fun j=>by simpa [zy,h] using e (q.symm j)⟩,rfl⟩
 . rintro ⟨Y,⟨hY,e⟩,rfl⟩;exact ⟨⟨Y,hY,rfl⟩,fun j=>by simp [zy,h,e]⟩
lemma kV (hH:Ze L) (p q:Perm (Fin 4)) (h0:p 0=0) (hp:p 1=1/\p 2=2\/p 1=2/\p 2=1):Ze (L.map (zq p q).toLinearMap)/\jf (L.map (zq p q).toLinearMap)=(jf L).map (zq p q).toLinearMap:=by
 have ⟨hL,h6,hr,h1,h2⟩:=hH;have K:zh (L.map (zq p q).toLinearMap) 0=(zh L 0).map (zq p q).toLinearMap:=wI h0;refine ⟨⟨zH hL p q,by rw [zF];exact h6,by rw [yN,h0];exact hr,?_,?_⟩,?_⟩
 . rw [K,yN];rcases hp with ⟨e,-⟩|⟨e,-⟩<;>rw [e]<;>assumption
 . rw [K,yN];rcases hp with ⟨-,e⟩|⟨-,e⟩<;>rw [e]<;>assumption
 . simp only [jf,zh];rw [wI h0];rcases hp with ⟨e,f⟩|⟨e,f⟩<;>rw [wI e,wI f];rw [inf_right_comm]
lemma YT (F:qy) (hH:Ze L) (hF1:finrank KD (jf L)=1) {a b:Fin 4} (hab:a≠b) (hE:(fun x:Fin 4×Fin 4=>vT a b 3 (x.2,x.1))∈L):False:=by
 have ⟨hL,h6,hr,_⟩:=id hH;have ⟨i,hi3,hi⟩:=Zi F hL h6 hab hE;have ⟨p,h0,h2,h3,hp⟩:∃p:Perm (Fin 4),p 0=0/\p 2=i/\p 3=3/\(p 1=1/\p 2=2\/p 1=2/\p 2=1):=by
  fin_cases i<;>simp at hi3
  . exact (kH hL hr hab hi).elim
  exacts [⟨swap 1 2,by decide⟩,⟨1,by decide⟩]
 obtain ⟨q,rfl,rfl⟩:∃q:Perm (Fin 4),q 0=a/\q 1=b:=⟨_,JJ a b hab⟩;have ⟨hH',hF'⟩:=kV hH p q h0 hp;have ⟨l,hS⟩:=ZX hH';set f:=(zq p q).toLinearMap;have e:∀i' j,f (fun x:Fin 4×Fin 4=>vT (q 0) (q 1) 3 (x.2,x.1)) (i',j)=if i'=3 then ![1,-1,0,0] j else 0:=fun i' j=>by
  have:p i'=3↔i'=3:=⟨fun h=>p.injective (h.trans h3.symm),fun h=>h▸h3⟩
  simp only [f,LinearEquiv.coe_coe,zy,vT,Prod.mk.injEq,Equiv.apply_eq_iff_eq,this];by_cases h:i'=3<;>fin_cases j<;>simp [h]
 have ⟨A,B,Q⟩:=Zf hS (by rw [hF',LinearEquiv.finrank_map_eq];exact hF1) (yt.2 ⟨mem_map_of_mem hE,fun j=>by rw [e];simp,fun j=>by rw [e];simp,fun j=>by rw [e];simp⟩) fun h=>by have:=e 3 0;rw [h] at this;simp at this
 exact JI Q (funext fun j=>by rw [zI,e];simp) fun T hT=>by obtain ⟨T,hT,rfl⟩:=hT;simp only [f,LinearEquiv.coe_coe,zy,h2];exact hi T hT
lemma YU (F:qy) (hH:Ze L) (hF1:finrank KD (jf L)=1):False:=by
 have ⟨l,hS⟩:=ZX hH;have ⟨W,hW,hW0⟩:=exists_mem_ne_zero_of_ne_bot (p:=jf L) fun h=>by rw [h,finrank_bot] at hF1;omega
 have ⟨A,B,Q⟩:=Zf hS hF1 hW hW0;have ⟨_,hsw,_⟩:=wo Q;have ⟨WL,w0,w1,w2⟩:=yt.1 hW;have hw:=xu Q.2.2.2.2.2.2.2.2.1;by_cases h4:∀j,W (3,j)≠0;· exact Jt Q h4
 push Not at h4;have ⟨h,hh⟩:=h4;by_cases h3:∀k,W (3,z8 h k)≠0;· exact YS F Q hh h3
 push Not at h3;have ⟨k,hk⟩:=h3;refine YT F hH hF1 (a:=z8 h (z6 k 0)) (b:=z8 h (z6 k 1)) (by fin_cases h<;>fin_cases k<;>decide) ?_
 convert L.smul_mem (W (3,z8 h (z6 k 0)))⁻¹ WL using 1;funext ⟨i,j⟩;simp only [yV,zI] at hsw hw;fin_cases i<;>simp [vT,w0,w1,w2];fin_cases h<;>fin_cases k<;>simp [z8,z6] at hh hk ⊢<;>fin_cases j<;>simp [hh,hk]<;>grind
def qA (a z:zu):KD:=a 0*z 0+a 1*z 1+a 2*z 2
def k7 (a b:zu):zu:=fun k=>qI (single k 1) a b
def vg (f g:zu):Prop:=f 0*g 1-f 1*g 0≠0\/f 0*g 2-f 2*g 0≠0\/f 1*g 2-f 2*g 1≠0
def x5 (a b c:zu):KD:=c 0*(a 1*b 2-a 2*b 1)-c 1*(a 0*b 2-a 2*b 0)+c 2*(a 0*b 1-a 1*b 0)
lemma YV (a b g h:zu) (c:KD):x5 a b (g-c•h)=x5 a b g-c*x5 a b h:=by simp [x5];ring
lemma vU (a b z:zu):qA (a+b) z=qA a z+qA b z:=by simp [qA];ring
lemma jZ (a b w:zu):qI a b w=qA (k7 a b) w:=by simp [qI,qA,k7];ring
lemma YW {f g:zu} (hi:∀s t:KD,s•f+t•g=0->s=0/\t=0):vg f g:=by
 by_contra h;unfold vg at h;push Not at h;by_cases f0:f=0
 . exact one_ne_zero (hi 1 0 (by simp [f0])).1
 rcases xq f0 with e|e|e
 . have:=(hi (g 0) (-f 0) (funext fun k=>by fin_cases k<;>simp<;>grind)).2;simp [e] at this
 . have:=(hi (g 1) (-f 1) (funext fun k=>by fin_cases k<;>simp<;>grind)).2;simp [e] at this
 . have:=(hi (g 2) (-f 2) (funext fun k=>by fin_cases k<;>simp<;>grind)).2;simp [e] at this
lemma JK {w1 w2 x c d:zu} (hm:vg w1 w2) (c1:qA c w1=0) (c2:qA c w2=0) (c3:qA c x=0) (d1:qA d w1=0) (d2:qA d w2=0) (d3:qA d x≠0):c=0:=by
 unfold vg qA at *;funext k;fin_cases k<;>simp<;>grind
lemma JL {w1 w2 c d:zu} (hm:vg w1 w2) (c1:qA c w1=0) (c2:qA c w2=0) (d1:qA d w1=0) (d2:qA d w2=0) (y:zu) (i:Fin 3):qA c y*d i=qA d y*c i:=by
 unfold vg qA at *;fin_cases i<;>simp<;>grind
lemma vV {w1 w2 g:zu} (hm:vg w1 w2) (h:x5 w1 w2 g=0):∃a b:KD,g=a•w1+b•w2:=by
 unfold x5 at h;rcases hm with m|m|m
 . exact ⟨(g 0*w2 1-g 1*w2 0)/(w1 0*w2 1-w1 1*w2 0),(w1 0*g 1-w1 1*g 0)/(w1 0*w2 1-w1 1*w2 0),funext fun k=>by fin_cases k<;>simp<;>field_simp<;>grind⟩
 . exact ⟨(g 0*w2 2-g 2*w2 0)/(w1 0*w2 2-w1 2*w2 0),(w1 0*g 2-w1 2*g 0)/(w1 0*w2 2-w1 2*w2 0),funext fun k=>by fin_cases k<;>simp<;>field_simp<;>grind⟩
 . exact ⟨(g 1*w2 2-g 2*w2 1)/(w1 1*w2 2-w1 2*w2 1),(w1 1*g 2-w1 2*g 1)/(w1 1*w2 2-w1 2*w2 1),funext fun k=>by fin_cases k<;>simp<;>field_simp<;>grind⟩
def ZZ (L:Submodule KD ze) (A W1 W2:ze):Prop:=A∈zh L 0/\W1∈jf L/\W2∈jf L/\¬(zI A 1=0/\zI A 2=0)/\(∀s t:KD,s•zI W1 3+t•zI W2 3=0->s=0/\t=0)/\∀T∈zh L 0,∃x y z:KD,T=x•A+y•W1+z•W2
def jT (L:Submodule KD ze) (l:(Fin 4->KD)→ₗ[KD]KD) (A W1 W2:ze):Prop:=ZW L l/\ZZ L A W1 W2/\qv A 3=0/\l (single 0 1)≠0
lemma JM (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hF:finrank KD (jf L)=2):∃A W1 W2,ZZ L A W1 W2:=by
 have hK:=y5 h6 hr;set φ:=(z9 1).prod (z9 2);have KF:zh L 0⊓LinearMap.ker φ=jf L:=by rw [LinearMap.ker_prod,jf,inf_assoc]
 have e:=zW φ (zh L 0);rw [KF,hF,hK] at e;let b:=Module.finBasisOfFinrankEq KD (jf L) hF;have ⟨A,hA,AF⟩:∃A∈zh L 0,A∉jf L:=by by_contra h;push Not at h;have:=finrank_mono (show zh L 0≤jf L from h);omega
 have hA0:φ A≠0:=fun h0=>AF (KF▸⟨hA,h0⟩)
 refine ⟨A,b 0,b 1,hA,(b 0).2,(b 1).2,fun ⟨h1,h2⟩=>hA0 (Prod.ext h1 h2),fun s t hst=>?_,fun T hT=>?_⟩
 . have:=Fintype.linearIndependent_iff.1 b.linearIndependent ![s,t] (by
    simp only [Fin.sum_univ_two];apply Subtype.ext;have ⟨_,a0,a1,a2⟩:=yt.1 (b 0).2;have ⟨_,c0,c1,c2⟩:=yt.1 (b 1).2
    funext ⟨i,j⟩;fin_cases i<;>simp [a0,a1,a2,c0,c1,c2];simpa [zI] using congrFun hst j)
   exact ⟨this 0,this 1⟩
 . have ⟨x,hx⟩:=Wl _ (by omega) (mem_map_of_mem hA) hA0 (mem_map_of_mem hT)
   have TF:T-x•A∈jf L:=KF▸⟨sub_mem hT (smul_mem _ x hA),LinearMap.mem_ker.2 (by rw [map_sub,map_smul,hx,sub_self])⟩
   have hr:=b.sum_repr ⟨_,TF⟩;simp only [Fin.sum_univ_two] at hr
   refine ⟨x,b.repr ⟨_,TF⟩ 0,b.repr ⟨_,TF⟩ 1,?_⟩;have:=congrArg Subtype.val hr;simp only [coe_add,coe_smul] at this;rw [add_assoc,this];abel
lemma jF (hL:zg L) {W1 W2} (h1:W1∈jf L) (h2:W2∈jf L) (hi:∀s t:KD,s•zI W1 3+t•zI W2 3=0->s=0/\t=0):vg (qv W1 3) (qv W2 3):=YW fun s t h=>hi s t (funext fun j=>by
 have ⟨a,a0,a1,a2⟩:=yt.1 h1;have ⟨b,b0,b1,b2⟩:=yt.1 h2;have u:=wn hL a;have v:=wn hL b;have x:=congrFun h 0;have y:=congrFun h 1;have z:=congrFun h 2;simp [Fin.sum_univ_four,a0,a1,a2,b0,b1,b2,zZ,zI,z8] at u v x y z;fin_cases j<;>simp [zI]<;>grind)
lemma JN (a b c d:Fin 4->KD):je a 0 c d=0/\je a b 0 d=0:=by simp [je]
lemma wC (hL:zg L) {A W X} (hA:A∈zh L 0) (hW:W∈jf L) (hX:X∈zP L):yM X X X W=0/\yM X A X W+yM X X A W=0/\yM X A A W=0:=by
 have ⟨AL,hA0⟩:=jL.1 hA;have ⟨WL,h0,h1,h2⟩:=yt.1 hW;have w:∀{Y},Y∈zP L-> yM Y Y Y W=0:=fun hY=>by have:=(kE hL hY WL h0).1;simp [yM,je,zI,h1,h2] at this ⊢;grind
 have a:=w hX;have b:=w (yo hX AL 1);have c:=w (yo hX AL (-1));simp only [yM,je,zI,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hA0] at a b c ⊢;exact ⟨a,by grind,by grind⟩
lemma JO (hS:ZW L l) (Q:ZZ L A W1 W2) (h0:l (single 0 1)≠0):∃A',jT L l A' W1 W2:=by
 have ⟨hA,hW1,hW2,hu,hi,hsp⟩:=Q;have ⟨AL,hA0⟩:=jL.1 hA;have ⟨hL1,w10,w11,w12⟩:=yt.1 hW1;have ⟨hL2,w20,w21,w22⟩:=yt.1 hW2;have hm:=jF hS.1.1 hW1 hW2 hi;by_cases d:x5 (qv W1 3) (qv W2 3) (qv A 3)=0
 . have ⟨a,b,e⟩:=vV hm d
   refine ⟨A-a•W1-b•W2,hS,⟨sub_mem (sub_mem hA (smul_mem _ a (jL.2 ⟨hL1,w10⟩))) (smul_mem _ b (jL.2 ⟨hL2,w20⟩)),hW1,hW2,?_,hi,fun T hT=>?_⟩,?_,h0⟩
   . convert hu using 3<;>funext j<;>simp [zI,w11,w21,w12,w22]
   . obtain ⟨x,y,z,rfl⟩:=hsp T hT;exact ⟨x,y+x*a,z+x*b,by simp only [smul_sub,smul_smul,add_smul];abel⟩
   . funext k;have:=congrFun e k;simp [zZ,zI] at this ⊢;grind
 . exfalso;have ⟨X,hX,x0,ha⟩:=yP hS (single 0 1)
   set c:=x5 (qv W1 3) (qv W2 3) (qv X 3)/x5 (qv W1 3) (qv W2 3) (qv A 3)
   have ⟨a,b,e⟩:=vV hm (g:=qv X 3-c•qv A 3) (by simp only [c,YV,div_mul_cancel₀ _ d,sub_self])
   refine (kF hS.1.1 (yo (yo (yo hX AL (-c)) hL1 (-a)) hL2 (-b)) (by rw [<-x0];funext j;simp [zI,hA0,w10,w20]) (by rw [wY hS.1.1 hL2,wY hS.1.1 hL1,wY hS.1.1 AL,ha];exact h0)).2.2 ?_
   funext k;have:=congrFun e k;simp [zZ,zI] at this ⊢;grind
lemma vW (C:jT L l A W1 W2) (hX:X∈zP L) (x0:zI X 0=single 0 1) (ha:y4 X≠0):qI (qv X 1) (qv X 2) (qv X 3)≠0/\qI (qv X 1) (qv X 2) (qv W1 3)=0/\qI (qv X 1) (qv X 2) (qv W2 3)=0/\k7 (qv A 1) (qv A 2)=0/\k7 (qv A 1) (qv X 2)+k7 (qv X 1) (qv A 2)=0:=by
 have ⟨⟨⟨hL,_⟩,_⟩,⟨hA,hW1,hW2,_,hi,_⟩,hp,_⟩:=C;have ⟨AL,hA0⟩:=jL.1 hA;have hm:=jF hL hW1 hW2 hi;have ⟨e1,g1,k1⟩:=wC hL hA hW1 hX;have ⟨e2,g2,k2⟩:=wC hL hA hW2 hX;simp only [yM,x0,xp] at e1 g1 k1 e2 g2 k2;have lv:∀t:KD,qI (qv X 1+t•qv A 1) (qv X 2+t•qv A 2) (qv X 3)=24*y4 X^4:=fun t=>by
  have e:=Qn hL (yo hX AL t);rw [wY hL AL,yM,show zI (X+t•A) 0=single 0 1 by rw [<-x0];funext j;simp [zI,hA0],xp] at e
  rw [<-e,show zZ (zI (X+t•A) 3) 0=qv X 3 by funext k;have:=congrFun hp k;simp [zZ,zI] at this ⊢;simp [this]];rfl
 have L0:=lv 0;have l1:=lv 1;have lm:=lv (-1);simp [qI] at L0 l1 lm;have d3:qI (qv X 1) (qv X 2) (qv X 3)≠0:=by rw [show qI _ _ _=24*y4 X^4 by simp [qI];grind];simp [ha]
 refine ⟨d3,e1,e2,?_,?_⟩<;>simp only [jZ] at e1 e2 g1 g2 k1 k2 d3
 . exact JK hm k1 k2 (by rw [<-jZ];simp [qI];grind) e1 e2 d3
 . exact JK hm (by rw [vU];exact g1) (by rw [vU];exact g2) (by rw [vU,<-jZ,<-jZ];simp [qI];grind) e1 e2 d3
lemma JP (C:jT L l A W1 W2) (h2:k7 (qv A 1) (qv A 2)=0):A (1,0)*A (2,1)+A (1,1)*A (2,0)=0/\A (1,0)*A (2,2)+A (1,2)*A (2,0)=0/\A (1,0)*A (2,3)+A (1,3)*A (2,0)=0:=by
 have ⟨hS,⟨hA,hW1,hW2,_,hi,_⟩,_⟩:=C;have hm:=jF hS.1.1 hW1 hW2 hi;have G:∀n,je (single n 1) (zI A 1) (zI A 2) (zI W1 3)=0/\je (single n 1) (zI A 1) (zI A 2) (zI W2 3)=0:=fun n=>by
  have ⟨X,hX,x0,_⟩:=yP hS (single n 1);rw [<-x0];exact ⟨(wC hS.1.1 hA hW1 hX).2.2,(wC hS.1.1 hA hW2 hX).2.2⟩
 have t:=congrFun h2;have t0:=t 0;have t1:=t 1;have t2:=t 2;have ⟨a1,b1⟩:=G 1;have ⟨a2,b2⟩:=G 2;have ⟨a3,b3⟩:=G 3;simp [vg,je,k7,qI,zZ,zI,z8] at t0 t1 t2 a1 b1 a2 b2 a3 b3 hm;grind
lemma ko (C:jT L l A W1 W2):(yV (zI W1 3)=0/\yV (zI W2 3)=0)/\yV (zI A 1)+yV (zI A 2)+A (3,0)=0/\yV (zI A 1)*yV (zI A 2)-wu (zI A 1) (zI A 2)+A (3,0)*(yV (zI A 1)-A (1,0)+(yV (zI A 2)-A (2,0)))=0/\wu (zI A 1+zI A 2) (zI W1 3)=0/\wu (zI A 1+zI A 2) (zI W2 3)=0:=by
 have ⟨⟨⟨hL,_⟩,_⟩,⟨hA,hW1,hW2,_⟩,hp,_⟩:=C;have ⟨AL,hA0⟩:=jL.1 hA;have ⟨a,a0,a1,a2⟩:=yt.1 hW1;have ⟨b,b0,b1,b2⟩:=yt.1 hW2;have s1:=wn hL a;have s2:=wn hL b;have p:=congrFun hp;have p1:=p 0;have p2:=p 1;have p3:=p 2;have ⟨_,g1,_⟩:=wC hL hA hW1 kD;have ⟨_,g2,_⟩:=wC hL hA hW2 kD;have ⟨c1,c2,_⟩:=kE hL kD AL hA0;simp [Fin.sum_univ_four,a0,a1,a2,b0,b1,b2] at s1 s2;simp [zZ,zI,z8] at p1 p2 p3;simp [yM,je,zI,qk,p1,p2,p3] at g1 g2 c1 c2;simp [yV,wu,zI];grind
lemma JQ (C:jT L l A W1 W2) (hU:qv A 1=0) (hV:qv A 2=0):False:=by
 have ⟨⟨⟨hL,h6,hr,_⟩,hl⟩,⟨hA,_,_,hu,_⟩,hp,h0⟩:=C;have hA':A∈zh L 0⊓LinearMap.ker (z7 0 0):=⟨hA,LinearMap.mem_ker.2 (by funext a b;rw [qL];fin_cases a<;>[have:=congrFun hU b;have:=congrFun hV b;have:=congrFun hp b]<;>simpa [zZ,zI,j5] using this)⟩
 rw [qs hL h6 hr hl h0,mem_bot] at hA';exact hu ⟨by rw [hA'];rfl,by rw [hA'];rfl⟩
lemma Q0 (C:jT L l A W1 W2) (hu0:A (1,0)=0) (hv0:A (2,0)=0) {k:Fin 3} {κ:KD} (hκ:κ≠0) (uk:qv A 1 k=0) (vk:qv A 2 k=0) (ua:qv A 1 (z6 k 0)≠0) (ub:qv A 1 (z6 k 1)≠0) (va:qv A 2 (z6 k 0)=κ*qv A 1 (z6 k 0)) (vb:qv A 2 (z6 k 1)=-κ*qv A 1 (z6 k 1)):False:=by
 have ⟨X,hX,x0,ha⟩:=yP C.1 (single 0 1);have ⟨d3,e1,e2,_,L3⟩:=vW C hX x0 (by rw [ha];exact C.2.2.2)
 have ⟨_,_,_,g1,g2⟩:=ko C;have ⟨⟨⟨hL,_⟩,_⟩,⟨_,hW1,hW2,_,hi,_⟩,_⟩:=C;have hm:=jF hL hW1 hW2 hi;have P:=JL hm (c:=k7 (qv X 1) (qv X 2)) (d:=qv A 1+qv A 2) (by rw [<-jZ];exact e1) (by rw [<-jZ];exact e2) (by simp [wu,qA,zZ,zI,z8,hu0,hv0] at g1 ⊢;grind) (by simp [wu,qA,zZ,zI,z8,hu0,hv0] at g2 ⊢;grind) (qv X 3)
 have pa:=P (z6 k 0);have pb:=P (z6 k 1);have za:=congrFun L3 (z6 k 0);have zb:=congrFun L3 (z6 k 1);rw [jZ] at d3;clear P L3 e1 e2 g1 g2 hX x0 ha hi hW1 hW2 hm;fin_cases k<;>simp [k7,qI,zZ,zI,qA,z6,z8] at pa pb za zb d3 uk vk ua ub va vb<;>grind
lemma xy {A:ze} {k:Fin 3} {i:Fin 4} (h:∀m,m≠k->A (i,m.succ)=0):∀j,j≠0->j≠k.succ->A (i,j)=0:=fun j h0 hk=>by obtain ⟨m,rfl⟩:=Fin.exists_succ_eq.2 h0;exact h m fun e=>hk (e▸rfl)
lemma JR {A:ze} (h:qv A 3=0):A (3,1)=0/\A (3,2)=0/\A (3,3)=0:=by have a:=congrFun h 0;have b:=congrFun h 1;have c:=congrFun h 2;simp [zZ,zI,z8] at a b c;exact ⟨a,b,c⟩
lemma Q7 (F:yQ) (C:jT L l A W1 W2) {k:Fin 3} (hu0:A (1,0)=0) (hv0:A (2,0)=0) (hU:∀m,m≠k->A (1,m.succ)=0) (hV:∀m,m≠k->A (2,m.succ)=0) (Uk:A (1,k.succ)≠0):False:=by
 have ⟨⟨hH,_⟩,⟨hA,hW1,hW2,_,hi,_⟩,hp,_⟩:=id C;have ⟨hL,_⟩:=id hH;have ⟨AL,hA0⟩:=jL.1 hA;have ⟨_,G1,G2,_⟩:=ko C;have ⟨a,a0,a1,a2⟩:=yt.1 hW1;have ⟨b,b0,b1,b2⟩:=yt.1 hW2;have s1:=wn hL a;have s2:=wn hL b;have hm:=jF hL hW1 hW2 hi;have ⟨p1,p2,p3⟩:=JR hp;have u:=xy hU;have v:=xy hV;simp [yV,wu,zI] at G1 G2;have σ:A (3,0)=0:=by fin_cases k<;>simp [u,v,hu0,hv0] at G1 G2<;>grind
 have ⟨hH',_⟩:=kV hH 1 (swap 0 k.succ) rfl (Or.inl ⟨rfl,rfl⟩);have E:y7∈L.map (zq 1 (swap 0 k.succ)).toLinearMap:=⟨(A (1,k.succ))⁻¹•A,L.smul_mem _ AL,funext fun ⟨i,j⟩=>by
  fin_cases k<;>simp [u,v,hu0,hv0,σ] at G1 Uk<;>fin_cases i<;>fin_cases j<;>simp [y7,zy,Equiv.swap_apply_def,hA0,u,v,hu0,hv0,σ,p1,p2,p3,Uk]<;>grind⟩
 have ⟨c,hc⟩:=F _ hH'.1 hH'.2.1 E hH'.2.2.1 fun h=>yR hH'.1 hH'.2.1 E fun T hT j hj=>by obtain ⟨m,rfl⟩:=Fin.exists_succ_eq.2 hj;exact h T hT m
 have x:=hc _ (mem_map_of_mem a);have y:=hc _ (mem_map_of_mem b);simp [vg,zZ,zI,z8,Fin.sum_univ_four,a0,a1,a2,b0,b1,b2] at hm s1 s2;simp [zy,a0,b0] at x y;fin_cases k<;>fin_cases c<;>simp [Equiv.swap_apply_def,z6] at x y<;>grind
lemma xz {w1 w2 n G:zu} (hm:vg w1 w2) (hn:n≠0) (h1:qA n w1=0) (h2:qA n w2=0) (h3:qA n G=0):∃a b:KD,G=a•w1+b•w2:=vV hm (by have:=xq hn;unfold vg x5 qA at *;grind)
lemma YX (hL:zg L) {W1 W2} {a b:KD} (h1:W1∈jf L) (h2:W2∈jf L) {x y:Fin 3} (hxy:x≠y) (h:(single x 1-single y 1:zu)=a•qv W1 3+b•qv W2 3):(fun z:Fin 4×Fin 4=>vT x.succ y.succ 3 (z.2,z.1))∈L:=by
 have ⟨c1,a0,a1,a2⟩:=yt.1 h1;have ⟨c2,b0,b1,b2⟩:=yt.1 h2;have s1:=wn hL c1;have s2:=wn hL c2;simp [Fin.sum_univ_four,a0,a1,a2,b0,b1,b2] at s1 s2;have e:=congrFun h;simp [zZ,zI,j5] at e;have e0:=e 0;have e1:=e 1;have e2:=e 2;convert add_mem (L.smul_mem a c1) (L.smul_mem b c2) using 1;funext ⟨i,j⟩;fin_cases x<;>fin_cases y<;>simp at hxy e0 e1 e2<;>fin_cases i<;>fin_cases j<;>simp [vT,a0,a1,a2,b0,b1,b2]<;>grind
set_option maxHeartbeats 400000 in
lemma Q8 (F:qy) (C:jT L l A W1 W2) {k:Fin 3} (hU:∀m,m≠k->A (1,m.succ)=0) (hV:∀m,m≠k->A (2,m.succ)=0) (hu0:A (1,0)≠0) (Uk:A (1,k.succ)≠0) (Vk:A (2,k.succ)≠0) (R:A (1,0)*A (2,k.succ)+A (1,k.succ)*A (2,0)=0):False:=by
 have ⟨⟨⟨hL,h6,hr,_⟩,_⟩,⟨hA,hW1,hW2,_,hi,_⟩,hp,_⟩:=id C;have ⟨AL,hA0⟩:=jL.1 hA;have ⟨_,G1,G2,G3,G4⟩:=ko C;have ⟨c1,a0,a1,a2⟩:=yt.1 hW1;have ⟨c2,b0,b1,b2⟩:=yt.1 hW2;have s1:=wn hL c1;have s2:=wn hL c2;have hm:=jF hL hW1 hW2 hi;have ⟨p1,p2,p3⟩:=JR hp;have u:=xy hU;have v:=xy hV;simp [yV,wu,zI,Fin.sum_univ_four,a0,a1,a2,b0,b1,b2] at G1 G2 G3 G4 s1 s2;have F5:∀x y:Fin 3,x≠y->∀a b:KD,(single x 1-single y 1:zu)=a•qv W1 3+b•qv W2 3->∃i:Fin 4,i≠3/\∀T∈L,T (i,x.succ)=T (i,y.succ):=fun x y hxy a b h=>Zi F hL h6 (fun e=>hxy (Fin.succ_injective _ e)) (YX hL hW1 hW2 hxy h)
 by_cases σ:A (3,0)=0
 . have hz:A (1,k.succ)+A (2,k.succ)≠0:=by fin_cases k<;>simp [u,v,σ] at G1 G2 R Uk Vk ⊢<;>grind
   have ⟨c,d,e⟩:=xz hm (n:=fun m=>if m=k then 2 else 1) (G:=single (z6 k 0) 1-single (z6 k 1) 1) (fun h=>by simpa using congrFun h k) (by fin_cases k<;>simp [qA,zZ,zI,z8,u,v,σ] at G1 G3 hz ⊢<;>grind) (by fin_cases k<;>simp [qA,zZ,zI,z8,u,v,σ] at G1 G4 hz ⊢<;>grind) (by fin_cases k<;>simp [qA,z6])
   have ⟨i,hi3,hiT⟩:=F5 _ _ (zN k).2.2 c d e
   have hE:c•W1+d•W2∈jf L:=add_mem (smul_mem _ c hW1) (smul_mem _ d hW2)
   have r:∀j,(c•W1+d•W2) (3,j)=if j=(z6 k 0).succ then 1 else if j=(z6 k 1).succ then -1 else 0:=fun j=>by
    have f:=congrFun e;simp [zZ,zI,j5] at f;have f0:=f 0;have f1:=f 1;have f2:=f 2;fin_cases k<;>fin_cases j<;>simp [z6] at f0 f1 f2 ⊢<;>grind
   have su:A (1,0)+A (1,k.succ)≠0:=fun h=>by fin_cases k<;>simp [u,v,σ] at G1 R hu0 Vk h<;>grind
   generalize c•W1+d•W2=E at hE r;have ⟨EL,e0,e1,e2⟩:=yt.1 hE
   refine kH hL hr (fun e=>(zN k).2.2 (Fin.succ_injective _ e)) fun T hT=>?_
   have g1:=(wC hL hA hE (yo kD hT 1)).2.1;have g2:=(wC hL hA hE (yo kD hT (-1))).2.1;have p1:=(qb hL (add_mem hT EL)).2.1;have p2:=(qb hL hT).2.1;have t:=hiT T hT
   fin_cases i
   . exact t
   all_goals fin_cases k<;>simp [z6] at r t ⊢<;>simp [yM,je,zI,qk,u,v,r] at g1 g2<;>simp [yl,Fintype.sum_prod_type,Fin.sum_univ_four,r,e0,e1,e2] at p1 p2<;>simp [u,v,σ] at G1 su<;>grind
 . have e:A (1,k.succ)+A (2,k.succ)=0/\A (2,0)=A (1,0):=by fin_cases k<;>simp [u,v] at G2 R Uk ⊢<;>grind
   have ⟨c,d,f⟩:=xz hm (n:=fun _=>1) (G:=single k 1-single (z6 k 0) 1) (fun h=>by simpa using congrFun h 0) (by fin_cases k<;>simp [qA,zZ,zI,z8,u,v] at G3 e ⊢<;>grind) (by fin_cases k<;>simp [qA,zZ,zI,z8,u,v] at G4 e ⊢<;>grind) (by fin_cases k<;>simp [qA,z6])
   have ⟨i,hi3,hiT⟩:=F5 k (z6 k 0) (zN k).1 c d f
   fin_cases i
   . exact kH hL hr (fun e=>(zN k).1 (Fin.succ_injective _ e)) hiT
   . exact Uk ((hiT A AL).trans (hU _ (zN k).1.symm))
   . exact Vk ((hiT A AL).trans (hV _ (zN k).1.symm))
   . exact hi3 rfl
lemma YY {w:zu} (hs:w 0+w 1+w 2=0) (hi:w 0^2+w 1^2+w 2^2=0) (h:w≠0):w 0≠0/\w 1≠0/\w 2≠0/\w 1^2-w 0^2≠0/\w 2^2-w 1^2≠0:=by have:=xq h;grind
lemma YZ {w dd e:zu} {D:Fin 3->zu} {ε:KD} (hs:w 0+w 1+w 2=0) (hi:w 0^2+w 1^2+w 2^2=0) (hw:w≠0) (T1:∀(x:zu) (τ:KD),τ*qI (fun i=>(∑j,D i j*x j)+τ*dd i) w w+((∑j,e j*x j)+τ*ε)*qI x w w=0) (T2:∀(x:zu) (τ:KD),τ*qI (fun i=>(∑j,D i j*x j)+τ*dd i) w (fun _=>1)+((∑j,e j*x j)+τ*ε)*qI x w (fun _=>1)-3*qI x (fun i=>(∑j,D i j*x j)+τ*dd i) w=0) (J1:(∑j,e j)+ε=1) (J2:∀i,(∑j,D i j)+dd i=1):False:=by
 have ⟨w0,w1,w2,q1,q2⟩:=YY hs hi hw;have he:∀m,e m=0:=fun m=>by have:=T1 (single m 1) 0;fin_cases m<;>simp [qI,Fin.sum_univ_three] at this⊢<;>grind
 have hε:ε=1:=by simpa [Fin.sum_univ_three,he] using J1
 have Q:∀x:zu,qI x (fun i=>∑j,D i j*x j) w=0:=fun x=>by have:=T2 x 0;simp [he] at this;grind
 have A1:∀x:zu,qI (fun i=>(∑j,D i j*x j)+dd i) w w+qI x w w=0:=fun x=>by simpa [he,hε] using T1 x 1
 have a0:=A1 0;have b0:=T2 0 1;have b1:=T2 (single 0 1) 1;have r:=Q (single 0 1);simp [qI,Pi.single_apply,he,hε] at a0 b0 b1 r;have r1:dd 1=dd 0:=by grind
 have r2:dd 2=dd 0:=by grind
 have hD:∀i,∑j,D i j=1-dd 0:=fun i=>by have:=J2 i;fin_cases i<;>simp [r1,r2] at this ⊢<;>grind
 have sk:=kn hs hD Q 0;simp [Fin.sum_univ_three] at sk;rw [r1,r2] at b1;have d0:dd 0=0:=by grind
 refine Jz (p:=fun k=>qI (single k 1) w w) (D:=D) (fun k=>by fin_cases k<;>assumption) hs (by simp [qI];grind) (by simp [qI];grind) (by simpa [d0] using hD) Q fun a=>?_
 have:=A1 (single a 1);fin_cases a<;>simp [qI,Fin.sum_univ_three,r1,r2,d0] at this⊢<;>grind
lemma K0 (C:jT L l A W1 W2) (hu:zI A 1=0):qA (fun i=>qv A 2 i-A (2,0)) (qv W1 3)=0/\qA (fun i=>qv A 2 i-A (2,0)) (qv W2 3)=0:=by
 have ⟨⟨s1,s2⟩,_,_,g1,g2⟩:=ko C;have ue:∀j,A (1,j)=0:=congrFun hu;simp [wu,yV,qA,zZ,zI,z8,ue] at s1 s2 g1 g2 ⊢;grind
lemma Zl (C:jT L l A W1 W2) (hu:zI A 1=0):False:=by
 have U:qv A 1=0:=by unfold qv;rw [hu];rfl
 by_cases hV:qv A 2=0;· exact JQ C U hV
 have ⟨X,hX,x0,ha⟩:=yP C.1 (single 0 1);have ⟨d3,e1,e2,_,L3⟩:=vW C hX x0 (by rw [ha];exact C.2.2.2)
 have ⟨⟨s1,s2⟩,G1,G2,_⟩:=ko C;have ⟨hS,⟨hA,hW1,hW2,_,hi,hsp⟩,_⟩:=id C;have ⟨⟨hL,_⟩,_⟩:=id hS;have hm:=jF hL hW1 hW2 hi;have ue:∀j,A (1,j)=0:=congrFun hu;rw [U] at L3;have Lx:k7 (qv X 1) (qv A 2)=0:=funext fun k=>by simpa [k7,ZY] using congrFun L3 k
 have ⟨k,hk⟩:∃k,qv A 2 k=0:=by by_contra h;push Not at h;exact d3 (by rw [xr h (congrFun Lx)];simp [qI])
 have ⟨n1,n2⟩:=K0 C hu;have P:=JL hm (c:=k7 (qv X 1) (qv X 2)) (by rw [<-jZ];exact e1) (by rw [<-jZ];exact e2) n1 n2 (qv X 3)
 have cv:qA (k7 (qv X 1) (qv X 2)) (qv A 2)=0:=by rw [<-jZ,show qI (qv X 1) (qv X 2) (qv A 2)=qI (qv X 1) (qv A 2) (qv X 2) by simp only [qI];ring,jZ,Lx];simp [qA]
 have q:=P;have q0:=P 0;have q1:=P 1;have q2:=P 2;rw [jZ] at d3;simp [yV,wu,zI,ue] at G1 G2;have nV:qA (fun i=>qv A 2 i-A (2,0)) (qv A 2)=0:=by simp [qA] at q0 q1 q2 cv d3 ⊢;grind
 have l0:=congrFun Lx 0;have l1:=congrFun Lx 1;have l2:=congrFun Lx 2;by_cases H:qv A 2 (z6 k 0)≠0/\qv A 2 (z6 k 1)≠0/\A (3,0)=0;swap
 . clear Lx L3 e1 e2 n1 n2 hm hi q0 q1 q2
   have R:∀i j,(qv A 2 i-A (2,0))*k7 (qv X 1) (qv X 2) j=(qv A 2 j-A (2,0))*k7 (qv X 1) (qv X 2) i:=fun i j=>by have a:=q i;have b:=q j;beta_reduce at a b;grind
   have cz:=xq (show k7 (qv X 1) (qv X 2)≠0 from fun h=>d3 (by rw [h];simp [qA]));have r01:=R 0 1;have r02:=R 0 2;have r12:=R 1 2;have hv:=xq hV
   clear R q nV cv d3;push Not at H
   fin_cases k<;>simp [k7,qI,zZ,zI,z6,z8] at r01 r02 r12 l0 l1 l2 cz hk hv H<;>grind (ringSteps:=2000000)
 have ⟨va,vb,σ⟩:=H;have ⟨_,_,a1,_⟩:=yt.1 hW1;have ⟨_,_,b1,_⟩:=yt.1 hW2;have hn:(fun i=>qv A 2 i-A (2,0))≠0:=fun h=>by have:=congrFun h k;simp [hk] at this;fin_cases k<;>simp [zZ,zI,z6,z8] at va vb G1 hk σ this<;>grind
 have ⟨a,b,hab⟩:=xz hm hn n1 n2 (G:=qv A 2) (by simp only [qA];fin_cases k<;>simp [qA,zZ,zI,z6,z8] at hk va vb G1 nV σ ⊢<;>grind)
 have ⟨c,d,hcd⟩:=xz hm hn n1 n2 (G:=fun i=>if i=k then -3 else 1) (by simp only [qA];fin_cases k<;>simp [qA,zZ,zI,z6,z8] at hk va vb G1 nV σ ⊢<;>grind)
 set h:=k.succ;have F:∀{x y:KD} {G:zu} (v:Fin 4->KD),G=x•qv W1 3+y•qv W2 3->v 0=-(G 0+G 1+G 2)-> zZ v 0=G->x•W1+y•W2∈jf L/\zI (x•W1+y•W2) 3=v:=fun {x y G} v e e0 e1=>⟨add_mem (smul_mem _ _ hW1) (smul_mem _ _ hW2),funext fun j=>by
  have f:=fun m=>congrFun e m;simp [zZ,zI,j5] at f;simp [yV,zI] at s1 s2;refine Fin.cases ?_ (fun m=>?_) j
  . rw [e0,f 0,f 1,f 2];simp [zI];grind
  . have:=congrFun e1 m;simp only [zZ,j5] at this;rw [this,f m];simp [zI]⟩
 have ⟨Wv,rv⟩:=F (zI A 2) hab (by fin_cases k<;>simp [zZ,zI,z8] at hk G1 σ ⊢<;>grind) rfl
 have ⟨Wz,rz⟩:=F (fun j=>if j=h then -3 else 1) hcd (by fin_cases k<;>norm_num [h]) (funext fun m=>by simp [zZ,h,j5])
 have vh:zI A 2 h=0:=by simp only [h,<-j5];exact hk
 have T1:∀X∈zP L,zI X 0 h*qI (zZ (zI X 1) h) (zZ (zI A 2) h) (zZ (zI A 2) h)+zI X 1 h*qI (zZ (zI X 0) h) (zZ (zI A 2) h) (zZ (zI A 2) h)=0:=fun X hX=>by
  have e:=(wC hL hA Wv hX).2.1;rw [yM,yM,hu,(JN _ 0 _ _).1,zero_add,rv,wm h,vh] at e;simpa using e
 have T2:∀X∈zP L,zI X 0 h*qI (zZ (zI X 1) h) (zZ (zI A 2) h) (fun _=>1)+zI X 1 h*qI (zZ (zI X 0) h) (zZ (zI A 2) h) (fun _=>1)-3*qI (zZ (zI X 0) h) (zZ (zI X 1) h) (zZ (zI A 2) h)=0:=fun X hX=>by
  have e:=(wC hL hA Wz hX).2.1;rw [yM,yM,hu,(JN _ 0 _ _).1,zero_add,rz,wm h,vh,show zZ (fun j=>if j=h then (-3:KD) else 1) h=fun _=>1 from funext fun m=>by simp [zZ,wp h m]] at e;simp at e;grind
 have s3:zZ (zI A 2) h 0+zZ (zI A 2) h 1+zZ (zI A 2) h 2=0/\zZ (zI A 2) h 0^2+zZ (zI A 2) h 1^2+zZ (zI A 2) h 2^2=0:=by fin_cases k<;>simp [h,qA,zZ,zI,z8,z6] at hk va vb G1 nV σ ⊢<;>grind
 choose M MV hM0 _ using fun m:Fin 4=>yP hS (single m 1)
 have m0:∀m j,M m (0,j)=(single m 1:Fin 4->KD) j:=fun m j=>congrFun (hM0 m) j
 have Y:∀(x:zu) (τ:KD),(∑m,x m•M (z8 h m))+τ•M h∈zP L:=fun x τ=>kG (sum_mem fun m _=>(zP L).smul_mem _ (MV _)) (MV h) τ
 have rI:∀(x:zu) (τ:KD) (r:Fin 4),zZ (zI ((∑m,x m•M (z8 h m))+τ•M h) r) h=fun i=>(∑j,M (z8 h j) (r,z8 h i)*x j)+τ*M h (r,z8 h i):=fun x τ r=>by funext i;simp [zZ,zI,Finset.sum_apply,mul_comm]
 have rh:∀(x:zu) (τ:KD) (r:Fin 4),zI ((∑m,x m•M (z8 h m))+τ•M h) r h=(∑j,M (z8 h j) (r,h)*x j)+τ*M h (r,h):=fun x τ r=>by simp [zI,Finset.sum_apply,mul_comm]
 have x0I:∀(x:zu) (τ:KD),(fun i=>(∑j,M (z8 h j) (0,z8 h i)*x j)+τ*M h (0,z8 h i))=x:=fun x τ=>by funext i;simp [m0,Pi.single_apply,kU,Ne.symm (wp h i)]
 have x0h:∀(x:zu) (τ:KD),(∑j,M (z8 h j) (0,h)*x j)+τ*M h (0,h)=τ:=fun x τ=>by simp [m0,wp]
 have hJ:qk-∑m,M m∈zh L 0:=by
  have z:∀j,(qk-∑m,M m) (0,j)=0:=fun j=>by simp [qk,Finset.sum_apply,m0,Pi.single_apply]
  exact jL.2 ⟨jQ hL (sub_mem kD (sum_mem fun m _=>MV m)) z,z⟩
 have J:∀j,M h (1,j)+∑m:Fin 3,M (z8 h m) (1,j)=1:=fun j=>by
  have ⟨x,y,z,e⟩:=hsp _ hJ;have e1:=congrFun e (1,j);have e2:=xt h (fun m=>M m (1,j));simp [qk,Fin.sum_univ_four,ue,a1,b1] at e1;simp [yV,zZ,Fin.sum_univ_three] at e2 ⊢;grind
 exact YZ (w:=zZ (zI A 2) h) (D:=fun i j=>M (z8 h j) (1,z8 h i)) (dd:=fun i=>M h (1,z8 h i)) (e:=fun j=>M (z8 h j) (1,h)) (ε:=M h (1,h)) s3.1 s3.2 (fun e=>va (by unfold qv;rw [jW e vh];rfl)) (fun x τ=>by have:=T1 _ (Y x τ);rwa [rh,rI,rh,rI,x0I,x0h] at this) (fun x τ=>by have:=T2 _ (Y x τ);rwa [rh,rI,rh,rI,x0I,x0h] at this) (by have:=J h;grind) fun i=>by have:=J (z8 h i);grind
lemma K1 (C:jT L l A W1 W2):jT (L.map (zq (swap 1 2) 1).toLinearMap) l (zq (swap 1 2) 1 A) (zq (swap 1 2) 1 W1) (zq (swap 1 2) 1 W2):=by
 have ⟨⟨hH,hl⟩,⟨hA,hW1,hW2,hu,hi,hsp⟩,hp,h0⟩:=C;have ⟨hH',hF⟩:=kV hH (swap 1 2) 1 (by decide) (Or.inr ⟨by decide,by decide⟩)
 have K:zh (L.map (zq (swap 1 2) 1).toLinearMap) 0=(zh L 0).map (zq (swap 1 2) 1).toLinearMap:=wI (by decide)
 have r:∀X i,zI (zq (swap 1 2) 1 X) i=zI X (swap 1 2 i):=fun _ _=>rfl
 refine ⟨⟨hH',?_⟩,⟨K▸mem_map_of_mem hA,hF▸mem_map_of_mem hW1,hF▸mem_map_of_mem hW2,?_,?_,?_⟩,?_,h0⟩
 . rintro a _ ⟨T,hT,rfl⟩;simpa [zy,show swap (1:Fin 4) 2 0=0 by decide] using hl a T hT
 . rw [r,r,show swap (1:Fin 4) 2 1=2 by decide,show swap (1:Fin 4) 2 2=1 by decide];exact fun ⟨a,b⟩=>hu ⟨b,a⟩
 . rw [r,r,show swap (1:Fin 4) 2 3=3 by decide];exact hi
 . rw [K];rintro _ ⟨T,hT,rfl⟩;obtain ⟨x,y,z,rfl⟩:=hsp T hT;exact ⟨x,y,z,by simp only [map_add,map_smul];rfl⟩
 . unfold qv;rw [r,show swap (1:Fin 4) 2 3=3 by decide];exact hp
lemma JS (F:qy) (G:yQ) (C:jT L l A W1 W2):False:=by
 by_cases hu:zI A 1=0;· exact Zl C hu
 by_cases hv:zI A 2=0;· exact Zl (K1 C) (funext fun j=>congrFun hv j)
 have ⟨X,hX,x0,ha⟩:=yP C.1 (single 0 1);have ⟨_,_,_,h2,_⟩:=vW C hX x0 (by rw [ha];exact C.2.2.2)
 have ⟨r1,r2,r3⟩:=JP C h2;have c:=congrFun h2;have c0:=c 0;have c1:=c 1;have c2:=c 2;have hu':=xu hu;have hv':=xu hv;simp [k7,qI,zZ,zI,z8] at c0 c1 c2 hu' hv';have E:∀f:zu,f 0=0->f 1=0->f 2=0->f=0:=fun f a b c=>funext fun i=>by fin_cases i<;>assumption
 by_cases hu0:A (1,0)=0<;>by_cases hv0:A (2,0)=0
 . rcases eq_or_ne (A (1,1)) 0 with a|a<;>rcases eq_or_ne (A (1,2)) 0 with b|b<;>rcases eq_or_ne (A (1,3)) 0 with d|d
   . simp [hu0,a,b,d] at hu'
   . exact Q7 G C (k:=2) hu0 hv0 (fun m h=>by fin_cases m<;>simp_all) (fun m h=>by fin_cases m<;>simp at h ⊢<;>grind) d
   . exact Q7 G C (k:=1) hu0 hv0 (fun m h=>by fin_cases m<;>simp_all) (fun m h=>by fin_cases m<;>simp at h ⊢<;>grind) b
   . refine Q0 C hu0 hv0 (k:=0) (κ:=A (2,2)/A (1,2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_<;>simp [zZ,zI,z6,z8]<;>(try field_simp)<;>grind
   . exact Q7 G C (k:=0) hu0 hv0 (fun m h=>by fin_cases m<;>simp_all) (fun m h=>by fin_cases m<;>simp at h ⊢<;>grind) a
   . refine Q0 C hu0 hv0 (k:=1) (κ:=A (2,1)/A (1,1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_<;>simp [zZ,zI,z6,z8]<;>(try field_simp)<;>grind
   . refine Q0 C hu0 hv0 (k:=2) (κ:=A (2,1)/A (1,1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_<;>simp [zZ,zI,z6,z8]<;>(try field_simp)<;>grind
   . grind
 . exact hu (funext fun j=>by fin_cases j<;>simp [zI,hu0]<;>grind)
 . exact hv (funext fun j=>by fin_cases j<;>simp [zI,hv0]<;>grind)
 . rcases eq_or_ne (A (1,1)) 0 with a|a<;>rcases eq_or_ne (A (1,2)) 0 with b|b<;>rcases eq_or_ne (A (1,3)) 0 with d|d
   . exact JQ C (E _ a b d) (E _ (by simp [zZ,zI,z8];grind) (by simp [zZ,zI,z8];grind) (by simp [zZ,zI,z8];grind))
   . exact Q8 F C (k:=2) (fun m h=>by fin_cases m<;>simp_all) (fun m h=>by fin_cases m<;>simp at h ⊢<;>grind) hu0 d (by grind) r3
   . exact Q8 F C (k:=1) (fun m h=>by fin_cases m<;>simp_all) (fun m h=>by fin_cases m<;>simp at h ⊢<;>grind) hu0 b (by grind) r2
   . grind
   . exact Q8 F C (k:=0) (fun m h=>by fin_cases m<;>simp_all) (fun m h=>by fin_cases m<;>simp at h ⊢<;>grind) hu0 a (by grind) r1
   all_goals grind
lemma K2 (F:qy) (G:yQ) (hH:Ze L) (hF2:finrank KD (jf L)=2):False:=by
 have ⟨l,hS⟩:=ZX hH;have ⟨j,hj⟩:=vR hS;have ⟨hH',hF'⟩:=kV hH 1 (swap 0 j) rfl (Or.inl ⟨rfl,rfl⟩);have hl:∀a,∀T∈L.map (zq 1 (swap 0 j)).toLinearMap,(l∘ₗLinearMap.funLeft KD KD (swap 0 j)) (fun k=>a+T (0,k))=a:=by
  rintro a _ ⟨T,hT,rfl⟩;rw [LinearMap.comp_apply];convert hS.2 a T hT using 2;funext m;simp [LinearMap.funLeft_apply,zy]
 have h0:(l∘ₗLinearMap.funLeft KD KD (swap 0 j)) (single 0 1)≠0:=by rw [LinearMap.comp_apply];convert hj using 2;funext m;simp [LinearMap.funLeft_apply,Pi.single_apply,Equiv.swap_apply_eq_iff]
 have ⟨A,W1,W2,Q⟩:=JM hH'.2.1 hH'.2.2.1 (by rw [hF',LinearEquiv.finrank_map_eq];exact hF2)
 have ⟨A',C⟩:=JO ⟨hH',hl⟩ Q h0;exact JS F G C
lemma JT:∀a b:Fin 4,a≠0->b≠0->(swap ((swap 1 a) 2) b*swap 1 a) 0=0:=by decide
theorem Q9 (hF5a:qy) (hF5b:yQ):yx:=by
 intro L hL h6 hr i' i'' h1 h2 h12 k1 k2;have ⟨e1,e2⟩:=Ju i' i'' h12;have e0:=JT i' i'' h1 h2;set L':=L.map (zq (swap ((swap 1 i') 2) i''*swap 1 i') 1:ze→ₗ[KD]ze);have K:=wI (S:=L) (q:=1) e0;have hH:Ze L':=⟨zH hL _ 1,by rw [zF];exact h6,by rw [yN,e0];exact hr,by rw [zh,K,yN,e1];exact k1,by rw [zh,K,yN,e2];exact k2⟩
 have:=zW (z9 1) (zh L' 0);have:=zW (z9 2) (zh L' 0⊓LinearMap.ker (z9 1));have:=y5 hH.2.1 hH.2.2.1;have:=finrank_mono (map_mono (f:=z9 2) (inf_le_left:zh L' 0⊓LinearMap.ker (z9 1)≤zh L' 0));have:finrank KD (jf L')=finrank KD (zh L' 0⊓LinearMap.ker (z9 1)⊓LinearMap.ker (z9 2):Submodule KD ze):=rfl;have:=hH.2.2.2.1;have:=hH.2.2.2.2;rcases (by omega:finrank KD (jf L')=1\/finrank KD (jf L')=2\/3≤finrank KD (jf L')) with h|h|h
 exacts [YU hF5a hH h,K2 hF5a hF5b hH h,YO hH.1 hH.2.1 h]
end
section
open Module Submodule LinearMap
def wq (L:Submodule KD ze):Prop:=zg L/\finrank KD L=6/\(∀ T∈L,T (0,0)=0)/\(∀ x y:Fin 4->KD,∃ T∈L,(∀ j,j≠0->T (0,j)=x j)/\∀ i,i≠0->T (i,0)=y i)/\(∀ T∈L,(∀ j,T (0,j)=0)->(∀ i,T (i,0)=0)->T=0)/\∀ T∈L,(∀ i,T (i,0)=0)->(∀ i j,i≠0->j≠0->T (i,j)=0)->T=0
def kW (L:Submodule KD ze) (R:Fin 4) (Z:ze):Prop:=Z∈L/\(∀ i,Z (i,0)=0)/\(∀ j,Z (R,j)=0)/\Z≠0/\∀ X∈L,(∀ i,X (i,0)=0)->(∀ j,X (R,j)=0)->∃ c:KD,X=c•Z
theorem y9 (p q:Equiv.Perm (Fin 4)) (X:ze) (i j):zq p q X (i,j)=X (p i,q j):=rfl
theorem jU {a b x:Fin 4} (h:x≠a) (k:x≠b):Equiv.swap a b x=x:=Equiv.swap_apply_of_ne_of_ne h k
theorem Zm {L:Submodule KD ze} {i X}:X∈zh L i↔X∈L/\∀ j,X (i,j)=0:=by simp [zh,funext_iff,zA]
theorem jy {L:Submodule KD ze} {j X}:X∈zC L j↔X∈L/\∀ i,X (i,j)=0:=by simp [zC,funext_iff,qF]
theorem Qo (l:(Fin 4->KD)→ₗ[KD]KD) (v:Fin 4->KD):l v=v 0*l (Pi.single 0 1)+v 1*l (Pi.single 1 1)+v 2*l (Pi.single 2 1)+v 3*l (Pi.single 3 1):=by
 have e:v=v 0•Pi.single 0 1+v 1•Pi.single 1 1+v 2•Pi.single 2 1+v 3•Pi.single 3 1:=by funext k;fin_cases k<;>simp
 conv_lhs=>rw [e];simp
theorem K3 {L:Submodule KD ze} (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) (hc:finrank KD (L.map (zD 0))=3) (hd:finrank KD (zm L 0 0)=0):wq L:=by
 have a:finrank KD (zh L 0)=3:=by have:=zW (z9 0) L;unfold zh;omega
 have b:finrank KD (zC L 0)=3:=by have:=zW (zD 0) L;unfold zC;omega
 have hI:zh L 0⊓zC L 0=⊥:=finrank_eq_zero.1 hd;have hS:=finrank_sup_add_finrank_inf_eq (zh L 0) (zC L 0);rw [hI,finrank_bot] at hS;have e:zh L 0⊔zC L 0=L:=eq_of_le_of_finrank_eq (sup_le inf_le_left inf_le_left) (by omega);have dec:∀ T∈L,∃ A∈zh L 0,∃ B∈zC L 0,A+B=T:=λ T h=>mem_sup.1 (e.symm▸h);have h0:∀ T∈L,T (0,0)=0:=λ T h=>by obtain ⟨A,hA,B,hB,rfl⟩:=dec T h;simp [(Zm.1 hA).2,(jy.1 hB).2]
 refine ⟨hL,h6,h0,λ x y=>?_,λ T h u v=>(mem_bot KD).1 (hI▸⟨Zm.2 ⟨h,u⟩,jy.2 ⟨h,v⟩⟩),λ T h u v=>(mem_bot KD).1 ((qS hL h6 hc (m:=LinearMap.proj 0) (λ a T hT=>by simp [h0 T hT]) (i:=0) (by simp))▸⟨jy.2 ⟨h,u⟩,mem_ker.2 (funext λ a=>funext λ c=>v _ _ (jp 0 a) (jp 0 c))⟩)⟩;have ⟨u,T,hT,p⟩:=(qu hL hr).1 λ j=>if j=0 then 0 else x j;have ⟨w,S,hS,q⟩:=(j3 hL hc).1 λ i=>if i=0 then 0 else y i;obtain ⟨A,hA,B,hB,rfl⟩:=dec T hT;obtain ⟨C,hC,D,hD,rfl⟩:=dec S hS;have a:=congrFun p 0;have b:=congrFun q 0;simp [(Zm.1 hA).2,(jy.1 hB).2,(Zm.1 hC).2,(jy.1 hD).2] at a b;exact ⟨B+C,add_mem (jy.1 hB).1 (Zm.1 hC).1,λ j hj=>by have:=congrFun p j;simp [hj,(Zm.1 hA).2,(Zm.1 hC).2] at this ⊢;grind,λ i hi=>by have:=congrFun q i;simp [hi,(jy.1 hB).2,(jy.1 hD).2] at this ⊢;grind⟩
theorem kp {L} (hD:wq L) {p q:Equiv.Perm (Fin 4)} (hp:p 0=0) (hq:q 0=0):wq (L.map (zq p q:ze→ₗ[KD]ze)):=by
 have ⟨hL,h6,h0,hx,hu,hi⟩:=hD;have P:∀{i},p i=0↔i=0:=⟨λ h=>p.injective (h.trans hp.symm),λ h=>h▸hp⟩;have Q:∀{i},q i=0↔i=0:=⟨λ h=>q.injective (h.trans hq.symm),λ h=>h▸hq⟩;refine ⟨zH hL p q,(zF L p q).trans h6,?_,λ x y=>?_,?_,?_⟩
 . rintro _ ⟨T,hT,rfl⟩;simpa [y9,hp,hq] using h0 T hT
 . have ⟨T,hT,h1,h2⟩:=hx (x∘q.symm) (y∘p.symm);exact ⟨_,⟨T,hT,rfl⟩,λ j hj=>by simp [y9,hp,h1 _ (Q.not.2 hj)],λ i hi=>by simp [y9,hq,h2 _ (P.not.2 hi)]⟩
 . rintro _ ⟨T,hT,rfl⟩ a b;rw [hu T hT (λ j=>by simpa [y9,hp] using a (q.symm j)) (λ i=>by simpa [y9,hq] using b (p.symm i)),map_zero]
 . rintro _ ⟨T,hT,rfl⟩ a b;rw [hi T hT (λ i=>by simpa [y9,hq] using a (p.symm i)) (λ i j c d=>by simpa [y9] using b (p.symm i) (q.symm j) (λ h=>c (by simpa [hp] using congrArg p h)) (λ h=>d (by simpa [hq] using congrArg q h))),map_zero]
theorem wZ {L:Submodule KD ze} {p q:Equiv.Perm (Fin 4)} (hq:q 0=0) {R Z} (h:kW L (p R) Z):kW (L.map (zq p q:ze→ₗ[KD]ze)) R (zq p q Z):=by
 have ⟨hZ,a,b,c,d⟩:=h;refine ⟨⟨Z,hZ,rfl⟩,λ i=>by simp [y9,hq,a],λ j=>b _,λ h=>c ((zq p q).map_eq_zero_iff.1 h),?_⟩;rintro _ ⟨X,hX,rfl⟩ e f;obtain ⟨k,rfl⟩:=d X hX (λ i=>by simpa [y9,hq] using e (p.symm i)) (λ j=>by simpa [y9] using f (q.symm j));exact ⟨k,map_smul _ _ _⟩
theorem x6 {L} (hD:wq L) {X:ze} (hX:X∈zP L):ql (λ i j=>X (i,j))=24*X (0,0)^4/\(X (0,0)=0->X∈L)/\∃ T∈L,X=T+X (0,0)•qk:=by
 obtain ⟨T,hT,_,hc,rfl⟩:=mem_sup.1 hX;obtain ⟨c,rfl⟩:=mem_span_singleton.1 hc;have e:(T+c•qk) (0,0)=c:=by simp [hD.2.2.1 T hT,qk]
 rw [yG hD.1 hX,e,map_add,map_smul,yf hD.1 hT,jI];exact ⟨by simp,λ h=>by simpa [h] using hT,T,hT,rfl⟩
theorem JU {L} (hD:wq L) (a:KD) (x y:Fin 4->KD):∃ X∈zP L,X (0,0)=a/\(∀ j,j≠0->X (0,j)=x j)/\∀ i,i≠0->X (i,0)=y i:=by
 have ⟨T,hT,h1,h2⟩:=hD.2.2.2.1 (λ j=>x j-a) (λ i=>y i-a);exact ⟨T+a•qk,add_mem_sup hT (mem_span_singleton.2 ⟨a,rfl⟩),by simp [hD.2.2.1 T hT,qk],λ j hj=>by simp [h1 j hj,qk],λ i hi=>by simp [h2 i hi,qk]⟩
theorem xA {L} (hD:wq L) {X:ze} (hX:X∈L) (hc:∀ i,X (i,0)=0) (i:Fin 4):zo (z7 i 0 X)=0:=by
 obtain ⟨Y,hY,h0,-,h2⟩:=JU hD (if 0=i then 1 else 0) 0 λ k=>if k=i then 1 else 0;have hY:∀ k,Y (k,0)=if k=i then 1 else 0:=λ k=>by rcases eq_or_ne k 0 with rfl|hk;exacts [h0,h2 k hk]
 refine (qE (zo (z7 i 0 Y)-24*Y (0,0)^4) (qm (z7 i 0 Y) (z7 i 0 X)) (qm (z7 i 0 X) (z7 i 0 Y)) _ λ t=>?_).2.2.2;have e:=(x6 hD (add_mem ‹_› ((zP L).smul_mem t (mem_sup_left hX)))).1;rw [ye _ 0] at e;simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hY,hc,mul_zero,add_zero] at e;rw [Finset.sum_eq_single i (λ b _ hb=>by simp [hb]) (by simp),← h0] at e;have e2:=ji 1 t (z7 i 0 Y) (z7 i 0 X);simp only [ite_true,one_mul,zt] at e e2;rw [e2] at e;grind
theorem JV {L} (hD:wq L):finrank KD (zC L 0)=3:=by
 let f:ze→ₗ[KD]Fin 3->KD:=LinearMap.pi λ k=>zf (0,k.succ);have e:=zW f (zC L 0);have t:(zC L 0).map f=⊤:=eq_top_iff.2 λ v _=>by
  have ⟨T,hT,a,b⟩:=hD.2.2.2.1 (Fin.cons 0 v) 0;exact ⟨T,jy.2 ⟨hT,λ i=>by rcases eq_or_ne i 0 with rfl|h;exacts [hD.2.2.1 T hT,by simpa using b i h]⟩,funext λ k=>by simpa [f,zf] using a k.succ k.succ_ne_zero⟩
 have u:(zC L 0⊓ker f:Submodule KD ze)=⊥:=eq_bot_iff.2 λ X h=>(mem_bot KD).2 (hD.2.2.2.2.1 X (jy.1 h.1).1 (λ j=>Fin.cases (hD.2.2.1 X (jy.1 h.1).1) (λ k=>by simpa [f,zf] using congrFun (mem_ker.1 h.2) k) j) (jy.1 h.1).2);rw [t,u,finrank_top,finrank_bot,finrank_fin_fun] at e;omega
theorem JW {L} (hD:wq L) {R:Fin 4} (hR:R≠0):finrank KD ((zC L 0).map (z9 R))≤2:=by
 obtain ⟨F,hF,-,h⟩:=hD.2.2.2.1 0 λ i=>if i=R then 1 else 0;have:finrank KD ((zC L 0).map (z9 R))<finrank KD (L.map (z9 R)):=finrank_lt_finrank_of_lt (lt_of_le_of_ne (map_mono inf_le_left) λ e=>by
  obtain ⟨X,hX,g⟩:z9 R F∈(zC L 0).map (z9 R):=e▸mem_map_of_mem hF;have:=congrFun g 0;simp [zA,h R hR,(jy.1 hX).2] at this)
 have:=yq hD.1 R;omega
theorem JX {L} (hD:wq L) {R:Fin 4} (h2:finrank KD ((zC L 0).map (z9 R))=2):∃ Z,kW L R Z:=by
 have e:=zW (z9 R) (zC L 0);rw [h2,JV hD] at e;have ⟨⟨Z,hZ⟩,h0,ha⟩:=finrank_eq_one_iff'.1 (show finrank KD ↥(zC L 0⊓ker (z9 R):Submodule KD ze)=1 by omega);refine ⟨Z,(jy.1 hZ.1).1,(jy.1 hZ.1).2,λ j=>congrFun (mem_ker.1 hZ.2) j,λ h=>h0 (Subtype.ext h),λ X hX a b=>?_⟩;have ⟨c,hc⟩:=ha ⟨X,jy.2 ⟨hX,a⟩,mem_ker.2 (funext b)⟩;exact ⟨c,(congrArg Subtype.val hc).symm⟩
theorem xB {L} (hD:wq L) {Z} (hK:kW L 1 Z):finrank KD (L.map (z9 1))=3/\∃ l:(Fin 4->KD)→ₗ[KD]KD,(∀ a,∀ T∈L,l (λ j=>a+T (1,j))=a)/\(l (Pi.single 1 1)≠0\/l (Pi.single 2 1)≠0\/l (Pi.single 3 1)≠0)/\(∀ X∈zP L,l (λ j=>X (1,j))=X (0,0))/\∀ a b c d g:KD,∃ X∈zP L,X (1,0)=0/\X (1,1)=a/\X (1,2)=b/\X (1,3)=c/\X (2,0)=d/\X (3,0)=g:=by
 have ⟨hZ,hc,h1,h0,hk⟩:=hK;have sp:∀ X∈L,(∀ i,X (i,0)=0)->(∀ j,X (1,j)=0)->X∈span KD {Z}:=λ X h a b=>let ⟨c,e⟩:=hk X h a b;mem_span_singleton.2 ⟨c,e.symm⟩;have s1:finrank KD (span KD {Z})=1:=finrank_span_singleton h0;have h3:finrank KD (L.map (z9 1))=3:=by
  let f:ze→ₗ[KD]KD × KD:=(zf (2,0)).prod (zf (3,0));have:=finrank_mono (show (L⊓ker (z9 1)⊓ker f:Submodule KD ze)≤span KD {Z} from λ X h=>sp X h.1.1 (λ i=>by fin_cases i;exacts [hD.2.2.1 X h.1.1,congrFun (mem_ker.1 h.1.2) 0,(Prod.ext_iff.1 (mem_ker.1 h.2)).1,(Prod.ext_iff.1 (mem_ker.1 h.2)).2]) λ j=>congrFun (mem_ker.1 h.1.2) j);have:=zW (z9 1) L;have:=zW f (L⊓ker (z9 1));have e:=finrank_le ((L⊓ker (z9 1)).map f);have:=yq hD.1 1;have:=hD.2.1;rw [finrank_prod,finrank_self] at e;omega
 obtain ⟨l,hl,-⟩:=(qu hD.1 h3).2;have hV:∀ X∈zP L,l (λ j=>X (1,j))=X (0,0):=λ X h=>by
  obtain ⟨-,-,T,hT,e⟩:=x6 hD h;generalize X (0,0)=c at e;subst e;simpa [qk,hD.2.2.1 T hT,add_comm] using hl c T hT
 have n:l (Pi.single 1 1)≠0\/l (Pi.single 2 1)≠0\/l (Pi.single 3 1)≠0:=by
  by_contra c;simp only [not_or,not_not] at c;obtain ⟨F,hF,-,e⟩:=hD.2.2.2.1 0 λ i=>if i=1 then 1 else 0;have a:=hl 1 0 L.zero_mem;have b:=hl 0 F hF;rw [Qo] at a b;simp [c,e 1 one_ne_zero] at a b;simp_all
 let φ:ze→ₗ[KD]Fin 6->KD:=LinearMap.pi λ k=>zf (![(1,0),(1,1),(1,2),(1,3),(2,0),(3,0)] k);have e:=zW φ (zP L);have h7:finrank KD L<finrank KD (zP L):=finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left λ h=>ku hD.1 (by rw [h];exact mem_sup_right (mem_span_singleton_self _)));have:=finrank_mono (show (zP L⊓ker φ:Submodule KD ze)≤span KD {Z} from λ X h=>by
  have k:=congrFun (mem_ker.1 h.2);simp [φ,zf,Fin.forall_fin_succ] at k;have r:∀ j,X (1,j)=0:=λ j=>by fin_cases j<;>simp [k]
  have z:=hV X h.1;rw [show (λ j=>X (1,j))=0 from funext r,map_zero] at z;exact sp X ((x6 hD h.1).2.1 z.symm) (λ i=>by fin_cases i<;>simp [k,← z]) r)
 have:=hD.2.1;have t:(zP L).map φ=⊤:=eq_top_of_finrank_eq (le_antisymm (finrank_le _) (by rw [finrank_fin_fun];omega));refine ⟨h3,l,hl,n,hV,λ a b c d g=>?_⟩;obtain ⟨X,hX,v⟩:![0,a,b,c,d,g]∈(zP L).map φ:=t▸mem_top;have v:=congrFun v;simp [φ,zf,Fin.forall_fin_succ] at v;exact ⟨X,hX,v⟩
theorem K4 (C:Fin 3->Fin 3->KD) (n:Fin 3->KD) {k} (hk:n k≠0) (h:∀ x y:Fin 3->KD,y 0=∑ b,n b*x b->∑ a,∑ b,y a*C a b*x b=0) (a b):C a b=0:=by
 have H:=qC (LinearMap.mk₂ KD (λ x y:Fin 3->KD=>∑ a,∑ b,y a*C a b*x b) (by intros;simp only [Pi.add_apply,Fin.sum_univ_three];ring) (by intros;simp only [Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three];ring) (by intros;simp only [Pi.add_apply,Fin.sum_univ_three];ring) (by intros;simp only [Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three];ring)) ⟨⟨λ x=>∑ b,n b*x b,by intros;simp only [Pi.add_apply,Fin.sum_univ_three];ring⟩,by intros;simp only [Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,RingHom.id_apply];ring⟩ (LinearMap.proj 0) (x0:=(n k)⁻¹•Pi.single k 1) (y0:=Pi.single 0 1) (by simp [Pi.single_apply,hk]) (by simp) λ x y e=>h x y (by simpa using e.symm);simpa [Pi.single_apply] using H (Pi.single b 1) (Pi.single a 1)
theorem Qa {L} (hD:wq L) {Z} (hK:kW L 1 Z):Z (2,2)*Z (3,3)+Z (2,3)*Z (3,2)=0/\Z (2,1)*Z (3,3)+Z (2,3)*Z (3,1)=0/\Z (2,1)*Z (3,2)+Z (2,2)*Z (3,1)=0/\Z (0,2)*Z (3,3)+Z (0,3)*Z (3,2)=0/\Z (0,1)*Z (3,3)+Z (0,3)*Z (3,1)=0/\Z (0,1)*Z (3,2)+Z (0,2)*Z (3,1)=0/\Z (0,2)*Z (2,3)+Z (0,3)*Z (2,2)=0/\Z (0,1)*Z (2,3)+Z (0,3)*Z (2,1)=0/\Z (0,1)*Z (2,2)+Z (0,2)*Z (2,1)=0:=by
 obtain ⟨-,l,-,n,hV,hs⟩:=xB hD hK;obtain ⟨hZ,hc,hr,-⟩:=hK;have key:∀ X∈zP L,X (1,0)=0->∑ a,∑ b,X (z8 1 a,0)*zn (z7 1 0 Z) a b*X (1,z8 0 b)=0:=λ X h e=>by
  have e1:=(x6 hD (add_mem h (mem_sup_left hZ))).1;have e2:=(x6 hD (sub_mem h (mem_sup_left hZ))).1;have e3:=(x6 hD h).1;simp only [zY,zs,zK,Fin.sum_univ_three,zt,Pi.add_apply,Pi.sub_apply] at e1 e2 e3 ⊢;simp [z8,z6,e,hc,hr] at e1 e2 e3 ⊢;grind
 obtain ⟨k,hk⟩:∃ k,l (Pi.single (z8 0 k) 1)≠0:=by rcases n with h|h|h;exacts [⟨0,h⟩,⟨1,h⟩,⟨2,h⟩]
 have c:=K4 _ (λ b=>l (Pi.single (z8 0 b) 1)) hk λ x y e=>by
  have ⟨X,hX,a0,a1,a2,a3,b2,b3⟩:=hs (x 0) (x 1) (x 2) (y 1) (y 2);have h0:X (0,0)=y 0:=by rw [← hV X hX,Qo,e];simp [Fin.sum_univ_three,z8,a0,a1,a2,a3];ring
  have:=key X hX a0;simp [Fin.sum_univ_three,z8,h0,a1,a2,a3,b2,b3] at this ⊢;linear_combination this
 have:=c 0 0;have:=c 0 1;have:=c 0 2;have:=c 1 0;have:=c 1 1;have:=c 1 2;have:=c 2 0;have:=c 2 1;have:=c 2 2;simp [zK,zt,z6,z8] at *;grind
theorem JY {E:Type} [AddCommGroup E] [Module KD E] (N:Submodule KD E) (f g h k m:E→ₗ[KD]KD) (H:∀ x∈N,f x*(g x*h x+k x*m x)=0) {y} (hy:y∈N) (hf:f y≠0) (x) (hx:x∈N):g x*h x+k x*m x=0:=by
 have:=H _ (N.add_mem hx (N.smul_mem 1 hy));have:=H _ (N.add_mem hx (N.smul_mem (-1) hy));have:=H _ (N.add_mem hx (N.smul_mem 2 hy));have:=H x hx;have:=H y hy;simp only [map_add,map_smul,smul_eq_mul] at *;grind
theorem Ko (N:Submodule KD ze) {j k:Fin 4} {r s m1 m2 n1 n3:KD} (hs:s≠0) (hm:m1≠0) (hr:r*m2+s*m1=0) (hn:n1≠0) (hG:∀ X∈N,(X (0,0)*m1+X (2,0)*r)*(X (1,k)*X (3,3)+X (1,3)*X (3,k))+(X (0,0)*m2+X (2,0)*s)*(X (1,j)*X (3,3)+X (1,3)*X (3,j))=0) (hI:∀ X∈N,X (1,3)=0->X (3,3)=0->(X (1,j)*X (3,k)+X (1,k)*X (3,j))*(X (0,0)*X (2,3)+X (2,0)*X (0,3))=24*X (0,0)^4) {P B Q:ze} (hP:P∈N) (hB:B∈N) (hQ:Q∈N) (eP:P (0,0)=n1/\P (2,0)=0/\P (1,j)=1/\P (1,k)=0/\P (1,3)=0) (eB:B (0,0)=0/\B (2,0)=1/\B (1,j)=0/\B (1,k)=0/\B (1,3)=0) (eQ:Q (0,0)=n3/\Q (2,0)=0/\Q (1,j)=0/\Q (1,k)=0/\Q (1,3)=1):False:=by
 have M:∀ b c:KD,P+b•Q+c•B∈N:=λ b c=>N.add_mem (N.add_mem hP (N.smul_mem b hQ)) (N.smul_mem c hB);have G:=λ b c=>hG _ (M b c);have I:=λ c=>hI _ (M 0 c);simp [eP,eB,eQ] at G I;have a:P (3,3)=0:=by have:=G 0 0;grind
 have b:B (3,3)=0:=by have:=G 0 1;have:=G 0 (-1);grind
 simp [a,b] at I;have:B (3,k)=0:=by have:=I 0;have:=I 1;have:=I (-1);have:=I 2;have:=I 3;grind
 have:=G 1 0;have:=G 1 1;have:=G 1 (-1);have:=G 2 0;have:=G 2 1;have:=G 2 (-1);have:=G 3 0;have:=G 3 1;have:=G 3 (-1);have:=I 0;grind
theorem Kp {L} (hD:wq L) {Z} (hK:kW L 1 Z) (h03:Z (0,3)=0) (h3:∀ j,Z (3,j)=0) (hr:Z (0,1)≠0) (hs:Z (0,2)≠0):False:=by
 obtain ⟨-,-,-,-,-,-,-,c21,c22⟩:=Qa hD hK;obtain ⟨-,l,hl,hn,hV,hsu⟩:=xB hD hK;have ⟨hZ,hc,h1,h0,hk⟩:=hK;have h23:Z (2,3)=0:=by grind
 have hm:Z (2,1)≠0:=λ h=>h0 (hD.2.2.2.2.2 Z hZ hc λ i j a b=>by have:Z (2,2)=0:=(by grind);fin_cases i<;>fin_cases j<;>grind);have m2:Z (2,2)≠0:=by grind
 by_cases n:l (Pi.single 1 1)=0/\l (Pi.single 2 1)=0
 . clear hV hsu;have k:∀ X∈L,(∀ i,X (i,0)=0)->X (1,3)=0:=λ X h c=>by have:=hl 0 X h;rw [Qo] at this;simp [c,n.1,n.2] at this;grind
   have F:∀ X∈L,(∀ i,X (i,0)=0)->X (2,3)*(X (0,1)*X (1,2)+X (0,2)*X (1,1))+X (0,3)*(X (1,1)*X (2,2)+X (1,2)*X (2,1))=0:=λ X h c=>by have:=xA hD h c 3;simp [zs,zt,z8,k X h c] at this;grind
   have ⟨E,hE,e1,e2⟩:=hD.2.2.2.1 (Pi.single 1 1) 0;have ⟨G,hG,g1,g2⟩:=hD.2.2.2.1 (Pi.single 3 1) 0;have Ec:∀ i,E (i,0)=0:=λ i=>by rcases eq_or_ne i 0 with rfl|h;exacts [hD.2.2.1 E hE,by simpa using e2 i h]
   have Gc:∀ i,G (i,0)=0:=λ i=>by rcases eq_or_ne i 0 with rfl|h;exacts [hD.2.2.1 G hG,by simpa using g2 i h]
   have x1:=e1 1 (by simp);have x2:=e1 2 (by simp);have x3:=e1 3 (by simp);have y1:=g1 1 (by simp);have y2:=g1 2 (by simp);have y3:=g1 3 (by simp);simp at x1 x2 x3 y1 y2 y3;have kz:∀ X∈L,(∀ i,X (i,0)=0)->X (1,1)=0->X (1,2)=0->X (0,2)=0->X=0:=λ X h c a b d=>by
    obtain ⟨κ,rfl⟩:=hk X h c (λ j=>by fin_cases j;exacts [c 1,a,b,k _ h c]);simp at d;simp [d.resolve_right hs]
   have hd:E (1,1)*G (1,2)-E (1,2)*G (1,1)≠0:=λ d=>by
    have u:=congrFun (kz _ (sub_mem (L.smul_mem (G (1,1)) hE) (L.smul_mem (E (1,1)) hG)) (λ i=>by simp [Ec,Gc]) (by simp;ring) (by simp;grind) (by simp [x2,y2])) (0,3);have w:=congrFun (kz _ (sub_mem (L.smul_mem (G (1,2)) hE) (L.smul_mem (E (1,2)) hG)) (λ i=>by simp [Ec,Gc]) (by simp;grind) (by simp;ring) (by simp [x2,y2])) (0,3);simp [x3,y3] at u w;have:=congrFun (kz E hE Ec u w x2) (0,1);simp [x1] at this
   have f1:=F E hE Ec;have f2:=F (E+Z) (add_mem hE hZ) (λ i=>by simp [Ec,hc]);have f3:=F G hG Gc;have f4:=F (G+Z) (add_mem hG hZ) (λ i=>by simp [Gc,hc]);have f5:=F (E+G) (add_mem hE hG) (λ i=>by simp [Ec,Gc]);have f6:=F (E+G+Z) (add_mem (add_mem hE hG) hZ) (λ i=>by simp [Ec,Gc,hc]);simp [x1,x2,x3,y1,y2,y3,h03,h1,h23] at f1 f2 f3 f4 f5 f6;clear F kz k hk hl e1 e2 g1 g2 Ec Gc hc h1 h3 hD hn;have e:E (2,3)=0:=by grind
   have:(E (1,1)*G (1,2)-E (1,2)*G (1,1))*(Z (2,1)+G (2,3)*Z (0,1))=0:=by grind
   have:(E (1,1)*G (1,2)-E (1,2)*G (1,1))*(Z (2,2)+G (2,3)*Z (0,2))=0:=by grind
   grind
 let N:=zP L⊓ker (zf (1,0))⊓ker (zf (3,0));have mN:∀ X∈N,X∈zP L/\X (1,0)=0/\X (3,0)=0:=λ X h=>⟨h.1.1,mem_ker.1 h.1.2,mem_ker.1 h.2⟩;have Nm:∀ X∈zP L,X (1,0)=0->X (3,0)=0->X∈N:=λ X h a b=>⟨⟨h,mem_ker.2 a⟩,mem_ker.2 b⟩;have hG:∀ X∈N,(X (0,0)*Z (2,1)+X (2,0)*Z (0,1))*(X (1,2)*X (3,3)+X (1,3)*X (3,2))+(X (0,0)*Z (2,2)+X (2,0)*Z (0,2))*(X (1,1)*X (3,3)+X (1,3)*X (3,1))=0:=λ X h=>by
  have ⟨v,a,b⟩:=mN X h;have e:=(x6 hD (add_mem v (mem_sup_left hZ))).1;have f:=(x6 hD v).1;simp [zY,zs,a,b,hc,h1,h3,h03,h23] at e f;grind
 have hI:∀ X∈N,X (1,3)=0->X (3,3)=0->(X (1,1)*X (3,2)+X (1,2)*X (3,1))*(X (0,0)*X (2,3)+X (2,0)*X (0,3))=24*X (0,0)^4:=λ X h c d=>by
  have ⟨v,a,b⟩:=mN X h;have:=(x6 hD v).1;simp [zY,zs,a,b,c,d] at this;grind
 have v0:∀ X∈zP L,X (1,0)=0->X (0,0)=X (1,1)*l (Pi.single 1 1)+X (1,2)*l (Pi.single 2 1)+X (1,3)*l (Pi.single 3 1):=λ X h a=>by rw [← hV X h,Qo];simp [a]
 have ⟨P,hP,a0,a1,a2,a3,a4,a5⟩:=hsu 1 0 0 0 0;have ⟨R,hR,d0,d1,d2,d3,d4,d5⟩:=hsu 0 1 0 0 0;have ⟨Q,hQ,q0,q1,q2,q3,q4,q5⟩:=hsu 0 0 1 0 0;have ⟨B,hB,b0,b1,b2,b3,b4,b5⟩:=hsu 0 0 0 1 0;have p:=v0 P hP a0;have r:=v0 R hR d0;have q:=v0 Q hQ q0;have b:=v0 B hB b0;simp [a1,a2,a3,d1,d2,d3,q1,q2,q3,b1,b2,b3] at p r q b;by_cases n1:l (Pi.single 1 1)=0
 . exact Ko (j:=2) (k:=1) (r:=Z (0,2)) (m2:=Z (2,1)) N hr m2 (by grind) (λ h=>n ⟨n1,h⟩) (λ X h=>by grind) (λ X h c d=>by grind) (Nm R hR d0 d5) (Nm B hB b0 b5) (Nm Q hQ q0 q5) ⟨r,d4,d2,d1,d3⟩ ⟨b,b4,b2,b1,b3⟩ ⟨q,q4,q2,q1,q3⟩
 . exact Ko (j:=1) (k:=2) N hs hm c22 n1 hG hI (Nm P hP a0 a5) (Nm B hB b0 b5) (Nm Q hQ q0 q5) ⟨p,a4,a1,a2,a3⟩ ⟨b,b4,b1,b2,b3⟩ ⟨q,q4,q1,q2,q3⟩
theorem K5 {L} (hD:wq L) {Z} (hK:kW L 1 Z) (h03:Z (0,3)=0) (hr:Z (0,1)≠0) (hs:Z (0,2)≠0):False:=by
 have C:=Qa hD hK;have c:=hK.2.1;have d:=hK.2.2.1;by_cases h2:Z (2,1)=0
 . exact Kp (kp hD (p:=Equiv.swap 2 3) (q:=1) (by decide) rfl) (wZ rfl (R:=1) (by rwa [jU (by simp) (by simp)])) (by simpa [y9,jU] using h03) (λ j=>by simp [y9];fin_cases j<;>grind) (by simpa [y9,jU] using hr) (by simpa [y9,jU] using hs)
 by_cases h3:Z (3,1)=0
 . exact Kp hD hK h03 (λ j=>by fin_cases j<;>grind) hr hs
 grind
theorem K6 {L} (hD:wq L) {Z} (hK:kW L 1 Z):∃ c:Fin 4,c≠0/\∀ i j,j≠c->Z (i,j)=0:=by
 have C:=Qa hD hK;obtain ⟨hZ,hc,h1,h0,-⟩:=id hK;have u:Z (0,1)=0->Z (0,2)=0->Z (0,3)=0->False:=λ a b d=>h0 (hD.2.2.2.2.1 Z hZ (λ j=>by fin_cases j;exacts [hc 0,a,b,d]) hc);have w:Z (2,1)=0->Z (2,2)=0->Z (2,3)=0->Z (3,1)=0->Z (3,2)=0->Z (3,3)=0->False:=λ a b d e f g=>h0 (hD.2.2.2.2.2 Z hZ hc λ i j x y=>by fin_cases i<;>fin_cases j<;>simp_all);have P:∀ c:Fin 4,c≠0->(∀ i j,i≠1->j≠0->j≠c->Z (i,j)=0)->∃ c:Fin 4,c≠0/\∀ i j,j≠c->Z (i,j)=0:=λ c h q=>⟨c,h,λ i j g=>by by_cases a:i=1;exact a▸h1 j;by_cases b:j=0;exact b▸hc i;exact q i j a b g⟩;rcases eq_or_ne (Z (0,1)) 0 with r1|r1<;>rcases eq_or_ne (Z (0,2)) 0 with r2|r2<;>rcases eq_or_ne (Z (0,3)) 0 with r3|r3
 . exact (u r1 r2 r3).elim
 . exact P 3 (by simp) λ i j a b g=>by fin_cases i<;>fin_cases j<;>grind
 . exact P 2 (by simp) λ i j a b g=>by fin_cases i<;>fin_cases j<;>grind
 . exact (K5 (kp hD (p:=1) (q:=Equiv.swap 1 3) rfl (by decide)) (wZ (p:=1) (by decide) hK) (by simpa [y9] using r1) (by simpa [y9] using r3) (by simpa [y9,jU] using r2)).elim
 . exact P 1 (by simp) λ i j a b g=>by fin_cases i<;>fin_cases j<;>grind
 . exact (K5 (kp hD (p:=1) (q:=Equiv.swap 2 3) rfl (by decide)) (wZ (p:=1) (by decide) hK) (by simpa [y9] using r2) (by simpa [y9,jU] using r1) (by simpa [y9] using r3)).elim
 . exact (K5 hD hK r3 r1 r2).elim
 . exact (w (by grind) (by grind) (by grind) (by grind) (by grind) (by grind)).elim
theorem Kq {L} (hD:wq L) {R:Fin 4} (hR:R≠0) {Z} (hK:kW L R Z):∃ c:Fin 4,c≠0/\∀ i j,j≠c->Z (i,j)=0:=by
 obtain ⟨c,hc,h⟩:=K6 (kp hD (p:=Equiv.swap 1 R) (q:=1) (jU (by simp) hR.symm) rfl) (wZ (p:=Equiv.swap 1 R) rfl (by rwa [Equiv.swap_apply_left]));exact ⟨c,hc,λ i j g=>by simpa [y9] using h ((Equiv.swap 1 R) i) j g⟩
theorem JZ {L} (hD:wq L) {X:ze} (h:X∈L) (c:∀ i,X (i,0)=0):X (0,1)*(X (2,2)*X (3,3)+X (2,3)*X (3,2))+X (0,2)*(X (2,1)*X (3,3)+X (2,3)*X (3,1))+X (0,3)*(X (2,1)*X (3,2)+X (2,2)*X (3,1))=0/\X (0,1)*(X (1,2)*X (3,3)+X (1,3)*X (3,2))+X (0,2)*(X (1,1)*X (3,3)+X (1,3)*X (3,1))+X (0,3)*(X (1,1)*X (3,2)+X (1,2)*X (3,1))=0/\X (0,1)*(X (1,2)*X (2,3)+X (1,3)*X (2,2))+X (0,2)*(X (1,1)*X (2,3)+X (1,3)*X (2,1))+X (0,3)*(X (1,1)*X (2,2)+X (1,2)*X (2,1))=0:=by
 have a:=xA hD h c 1;have b:=xA hD h c 2;have d:=xA hD h c 3;simp [zs,zt,z8] at a b d;grind
theorem Qc {L} (hL:zg L) (h6:finrank KD L=6) {i:Fin 4} (h3:finrank KD (L.map (z9 i))=3) {l:(Fin 4->KD)→ₗ[KD]KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (i,j))=a) {Y:ze} (hY:Y∈L) (h0:Y≠0) {c:Fin 4} (hc:∀ a b,b≠c->Y (a,b)=0):l (Pi.single c 1)=0:=by
 by_contra n;by_cases y:Y (i,c)=0
 . exact h0 ((mem_bot KD).1 (qs hL h6 h3 hl n▸⟨Zm.2 ⟨hY,λ b=>by by_cases h:b=c;exacts [h▸y,hc _ _ h]⟩,mem_ker.2 (funext λ a=>funext λ b=>hc _ _ (jp c b))⟩))
 . have:=hl 0 Y hY;rw [show (λ j=>0+Y (i,j))=Y (i,c)•Pi.single c 1 from funext λ j=>by by_cases h:j=c<;>simp [h,hc]] at this;simp_all
theorem Kr {L} (hD:wq L) {Z} (hK:kW L 1 Z) {Y W:ze} (a:Y∈L) (b:Y≠0) (p:∀ i j,j≠1->Y (i,j)=0) (c:W∈L) (d:W≠0) (q:∀ i j,j≠2->W (i,j)=0) (X) (h:X∈L) (e:X (1,0)=0):X (1,3)=0:=by
 obtain ⟨h3,l,hl,n,-⟩:=xB hD hK;have:=Qc hD.1 hD.2.1 h3 hl a b p;have:=Qc hD.1 hD.2.1 h3 hl c d q;have:=hl 0 X h;rw [Qo] at this;simp_all
theorem Ks {L} (hD:wq L) {Z W} (hK:kW L 1 Z) (pZ:∀ i j,j≠1->Z (i,j)=0) (hz:Z (2,1)≠0) (hW:kW L 2 W) (pW:∀ i j,j≠2->W (i,j)=0):False:=by
 have r1:=Kr hD hK hK.1 hK.2.2.2.1 pZ hW.1 hW.2.2.2.1 pW;have r2:=Kr (kp hD (p:=Equiv.swap 1 2) (q:=1) (by decide) rfl) (wZ (p:=Equiv.swap 1 2) rfl (R:=1) (by rwa [Equiv.swap_apply_left])) (mem_map_of_mem hK.1) (λ h=>hK.2.2.2.1 ((zq _ 1).map_eq_zero_iff.1 h)) (λ i j h=>by simpa [y9] using pZ _ j h) (mem_map_of_mem hW.1) (λ h=>hW.2.2.2.1 ((zq _ 1).map_eq_zero_iff.1 h)) (λ i j h=>by simpa [y9] using pW _ j h);have r2:∀ X∈L,X (2,0)=0->X (2,3)=0:=λ X h e=>by simpa [y9] using r2 _ (mem_map_of_mem h) (by simpa [y9] using e)
 have ⟨E,hE,e1,e2⟩:=hD.2.2.2.1 (Pi.single 3 1) 0;have q:=JY (zC L 0) (zf (0,3)) (zf (1,1)) (zf (2,2)) (zf (1,2)) (zf (2,1)) (λ X h=>by have c:=jy.1 h;have:=(JZ hD c.1 c.2).2.2;rw [r1 X c.1 (c.2 1),r2 X c.1 (c.2 2)] at this;simp only [zf,proj_apply];grind) (jy.2 ⟨hE,λ i=>by rcases eq_or_ne i 0 with rfl|h;exacts [hD.2.2.1 E hE,by simpa using e2 i h]⟩) (by have:=e1 3 (by simp);simp at this;simp [zf,this]);have:=q _ ((zC L 0).add_mem (jy.2 ⟨hK.1,hK.2.1⟩) (jy.2 ⟨hW.1,hW.2.1⟩));simp [zf,hK.2.2.1,hW.2.2.1,pZ 2 2,pW 1 1,hz] at this;have ⟨κ,e⟩:=hK.2.2.2.2 W hW.1 hW.2.1 λ j=>by by_cases h:j=2;exact h▸this;exact pW 1 j h
 exact hW.2.2.2.1 (hD.2.2.2.2.1 W hW.1 (λ j=>by by_cases h:j=2;rw [h,e];simp [pZ 0 2];exact pW 0 j h) hW.2.1)
theorem Kt {L} (hD:wq L) {Z} (hK:kW L 1 Z) (pZ:∀ i j,j≠1->Z (i,j)=0) (hz:Z (2,1)≠0):False:=by
 have hZ:=jy.2 ⟨hK.1,hK.2.1⟩;rcases Nat.lt_or_ge (finrank KD ((zC L 0).map (z9 2))) 2 with h|h
 . obtain ⟨h3,l,hl,n,-⟩:=xB hD hK;have n1:=Qc hD.1 hD.2.1 h3 hl hK.1 hK.2.2.2.1 pZ;have e:=eq_of_le_of_finrank_le ((span_singleton_le_iff_mem _ _).2 (mem_map_of_mem hZ)) (by rw [finrank_span_singleton (λ h=>hz (congrFun h 1):z9 2 Z≠0)];omega);have r:∀ X∈zC L 0,X (2,2)=0/\X (2,3)=0:=λ X h=>by
    have:z9 2 X∈span KD {z9 2 Z}:=e▸mem_map_of_mem h;have ⟨c,hc⟩:=mem_span_singleton.1 this;exact ⟨by simpa [zA,pZ 2 2] using (congrFun hc 2).symm,by simpa [zA,pZ 2 3] using (congrFun hc 3).symm⟩
   have q:=JY (zC L 0) (zf (2,1)) (zf (0,2)) (zf (1,3)) (zf (0,3)) (zf (1,2)) (λ X h=>by have c:=jy.1 h;have:=(JZ hD c.1 c.2).2.2;rw [(r X h).1,(r X h).2] at this;simp only [zf,proj_apply];grind) hZ hz;have ⟨E,hE,e1,e2⟩:=hD.2.2.2.1 (Pi.single 2 1) 0;have ⟨G,hG,g1,g2⟩:=hD.2.2.2.1 (Pi.single 3 1) 0;have Ec:∀ i,E (i,0)=0:=λ i=>by rcases eq_or_ne i 0 with rfl|h;exacts [hD.2.2.1 E hE,by simpa using e2 i h]
   have Gc:∀ i,G (i,0)=0:=λ i=>by rcases eq_or_ne i 0 with rfl|h;exacts [hD.2.2.1 G hG,by simpa using g2 i h]
   have x2:=e1 2 (by simp);have x3:=e1 3 (by simp);have y2:=g1 2 (by simp);have y3:=g1 3 (by simp);simp at x2 x3 y2 y3;have kz:∀ X∈zC L 0,(∀ j,X (1,j)=0)->X (0,2)=0/\X (0,3)=0:=λ X h r=>by obtain ⟨κ,rfl⟩:=hK.2.2.2.2 X (jy.1 h).1 (jy.1 h).2 r;simp [pZ 0 2,pZ 0 3]
   have hE:=jy.2 ⟨hE,Ec⟩;have hG:=jy.2 ⟨hG,Gc⟩;have a:=q E hE;have b:=q G hG;have c:=q _ ((zC L 0).add_mem hE hG);have d:=hl 0 E (jy.1 hE).1;have f:=hl 0 G (jy.1 hG).1;rw [Qo] at d f;simp [zf,x2,x3,y2,y3,Ec,Gc,n1] at a b c d f;by_cases g:E (1,2)=0
   . have A:=kz _ ((zC L 0).sub_mem ((zC L 0).smul_mem (G (1,1)) hE) ((zC L 0).smul_mem (E (1,1)) hG)) λ j=>by fin_cases j<;>simp [Ec,Gc,g]<;>grind
     simp [x2,x3,y2,y3] at A;have B:=kz E hE λ j=>by fin_cases j<;>simp [Ec,g]<;>grind
     simp [x2] at B
   . grind
 . have ⟨W,hW⟩:=JX hD (le_antisymm (JW hD (by simp)) h);have ⟨k,k0,pk⟩:=Kq hD (by simp) hW;fin_cases k
   . exact k0 rfl
   . have X:Z (0,1)•W-W (0,1)•Z=0:=hD.2.2.2.2.1 _ (sub_mem (L.smul_mem _ hW.1) (L.smul_mem _ hK.1)) (λ j=>by by_cases h:j=1;subst h;simp;ring;simp [pk 0 j h,pZ 0 j h]) λ i=>by simp [hK.2.1,hW.2.1]
     have:=congrFun X (2,1);simp [hW.2.2.1,hz] at this;exact hW.2.2.2.1 (hD.2.2.2.2.1 W hW.1 (λ j=>by by_cases h:j=1;exact h▸this;exact pk 0 j h) hW.2.1)
   . exact Ks hD hK pZ hz hW pk
   . exact Ks (kp hD (p:=1) (q:=Equiv.swap 2 3) rfl (by decide)) (wZ (p:=1) (by decide) (R:=1) hK) (λ i j h=>by simpa [y9] using pZ i _ λ e=>h (by simpa [jU] using congrArg (Equiv.swap 2 3) e)) (by simpa [y9,jU] using hz) (wZ (p:=1) (by decide) (R:=2) hW) (λ i j h=>by simpa [y9] using pk i _ λ e=>h (by simpa using congrArg (Equiv.swap 2 3) e))
theorem KA {L} (hD:wq L) {Z} (hK:kW L 1 Z) (pZ:∀ i j,j≠1->Z (i,j)=0):False:=by
 by_cases h2:Z (2,1)=0;by_cases h3:Z (3,1)=0
 . exact hK.2.2.2.1 (hD.2.2.2.2.2 Z hK.1 hK.2.1 λ i j a b=>by by_cases c:j=1;subst c;fin_cases i<;>simp_all [hK.2.2.1 1];exact pZ i j c)
 . exact Kt (kp hD (p:=Equiv.swap 2 3) (q:=1) (by decide) rfl) (wZ rfl (R:=1) (by rwa [jU (by simp) (by simp)])) (λ i j h=>by simpa [y9] using pZ _ j h) (by simpa [y9] using h3)
 . exact Kt hD hK pZ h2
theorem K7 {L} (hD:wq L) {h k:Fin 4} (a:finrank KD ((zC L 0).map (z9 h))≤1) (b:finrank KD ((zC L 0).map (z9 k))≤1):∃ Y∈L,Y≠0/\(∀ i,Y (i,0)=0)/\(∀ j,Y (h,j)=0)/\∀ j,Y (k,j)=0:=by
 have:=zW (z9 h) (zC L 0);have e:=zW (z9 k) (zC L 0⊓ker (z9 h));have:=finrank_mono (map_mono (f:=z9 k) (inf_le_left:(zC L 0⊓ker (z9 h):Submodule KD ze)≤_));have:=JV hD;obtain ⟨Y,⟨⟨u,v⟩,w⟩,z⟩:=exists_mem_ne_zero_of_ne_bot (p:=zC L 0⊓ker (z9 h)⊓ker (z9 k)) λ z=>by rw [z,finrank_bot] at e;omega
 exact ⟨Y,(jy.1 u).1,z,(jy.1 u).2,λ j=>congrFun (mem_ker.1 v) j,λ j=>congrFun (mem_ker.1 w) j⟩
theorem Qe {L} {S:Fin 4} (hS:finrank KD ((zC L 0).map (z9 S))≤1) {Y:ze} (hY:Y∈L) (c:∀ i,Y (i,0)=0) (n:Y (S,1)≠0\/Y (S,2)≠0\/Y (S,3)≠0) (X) (h:X∈L) (d:∀ i,X (i,0)=0):∃ μ:KD,∀ j,X (S,j)=μ*Y (S,j):=by
 have e:=eq_of_le_of_finrank_le ((span_singleton_le_iff_mem _ _).2 (mem_map_of_mem (jy.2 ⟨hY,c⟩))) (by rw [finrank_span_singleton (λ h=>by rcases n with n|n|n;exacts [n (congrFun h 1),n (congrFun h 2),n (congrFun h 3)]:z9 S Y≠0)];exact hS);have:z9 S X∈span KD {z9 S Y}:=e▸mem_map_of_mem (jy.2 ⟨h,d⟩);have ⟨μ,e⟩:=mem_span_singleton.1 this;exact ⟨μ,λ j=>(congrFun e j).symm⟩
theorem Qg {L:Submodule KD ze} {h k:Fin 4} (hrp:∀ X∈L,(∀ i,X (i,0)=0)->X (0,1)*(X (h,2)*X (k,3)+X (h,3)*X (k,2))+X (0,2)*(X (h,1)*X (k,3)+X (h,3)*X (k,1))+X (0,3)*(X (h,1)*X (k,2)+X (h,2)*X (k,1))=0) {Y W:ze} (a:Y∈L) (c:∀ i,Y (i,0)=0) (r:∀ j,Y (k,j)=0) (b:W∈L) (d:∀ i,W (i,0)=0) (s:∀ j,W (h,j)=0) (u:∀ X∈L,(∀ i,X (i,0)=0)->∃ μ:KD,∀ j,X (h,j)=μ*Y (h,j)) (v:∀ X∈L,(∀ i,X (i,0)=0)->∃ μ:KD,∀ j,X (k,j)=μ*W (k,j)) (E) (e:E∈L) (f:∀ i,E (i,0)=0):E (0,1)*(Y (h,2)*W (k,3)+Y (h,3)*W (k,2))+E (0,2)*(Y (h,1)*W (k,3)+Y (h,3)*W (k,1))+E (0,3)*(Y (h,1)*W (k,2)+Y (h,2)*W (k,1))=0:=by
 have A:=hrp _ (add_mem a b) (by simp [c,d]);have B:=hrp _ (add_mem a (L.smul_mem 2 b)) (by simp [c,d]);have ⟨μ,p⟩:=u E e f;have ⟨ν,q⟩:=v E e f;have I:=hrp (E+(1-μ)•Y+(1-ν)•W) (add_mem (add_mem e (L.smul_mem _ a)) (L.smul_mem _ b)) (by simp [f,c,d]);simp [p,q,r,s] at A B I;grind
theorem K8 {L} (hD:wq L) {c:Fin 4} (hc:c≠0) (h:∀ a b d:KD,∃ X∈L,(∀ i,X (i,0)=0)/\X (1,c)=a/\X (2,c)=b/\X (3,c)=d):False:=by
 obtain ⟨M,hM,m0,-,mc⟩:=JU hD 1 0 0;have ⟨X,hX,xc,a,b,d⟩:=h (-M (1,c)) (-M (2,c)) (-M (3,c));have:=(x6 hD (add_mem hM (mem_sup_left hX))).1;fin_cases c<;>simp_all [zY,zs]
theorem KB {L} (hD:wq L) (hr:∀ R:Fin 4,R≠0->finrank KD ((zC L 0).map (z9 R))≤1):False:=by
 have nz:∀ Y∈L,Y≠0->(∀ i,Y (i,0)=0)->∀ S:Fin 4,(∀ i,i≠0->i≠S->∀ j,Y (i,j)=0)->Y (S,1)≠0\/Y (S,2)≠0\/Y (S,3)≠0:=λ Y a b c S h=>by
  by_contra n;simp only [not_or,not_not] at n;exact b (hD.2.2.2.2.2 Y a c λ i j u v=>by by_cases w:i=S;subst w;fin_cases j<;>simp_all;exact h i u w j)
 have ⟨Y1,a1,b1,c1,d1,e1⟩:=K7 hD (hr 2 (by simp)) (hr 3 (by simp));have ⟨Y2,a2,b2,c2,d2,e2⟩:=K7 hD (hr 1 (by simp)) (hr 3 (by simp));have ⟨Y3,a3,b3,c3,d3,e3⟩:=K7 hD (hr 1 (by simp)) (hr 2 (by simp));have n1:=nz Y1 a1 b1 c1 1 λ i u w=>by fin_cases i<;>simp_all
 have n2:=nz Y2 a2 b2 c2 2 λ i u w=>by fin_cases i<;>simp_all
 have n3:=nz Y3 a3 b3 c3 3 λ i u w=>by fin_cases i<;>simp_all
 have s1:=Qe (hr 1 (by simp)) a1 c1 n1;have s2:=Qe (hr 2 (by simp)) a2 c2 n2;have s3:=Qe (hr 3 (by simp)) a3 c3 n3;have P:=Qg (λ X h c=>(JZ hD h c).2.2) a1 c1 d1 a2 c2 d2 s1 s2;have Q:=Qg (λ X h c=>(JZ hD h c).2.1) a1 c1 e1 a3 c3 d3 s1 s3;have R:=Qg (λ X h c=>(JZ hD h c).1) a2 c2 e2 a3 c3 e3 s2 s3;have E:∀ m:Fin 4,∃ E∈L,(∀ i,E (i,0)=0)/\∀ j,j≠0->E (0,j)=if j=m then 1 else 0:=λ m=>by
  have ⟨E,h,a,b⟩:=hD.2.2.2.1 (Pi.single m 1) 0;exact ⟨E,h,λ i=>by rcases eq_or_ne i 0 with rfl|g;exacts [hD.2.2.1 E h,by simpa using b i g],λ j g=>by simpa [Pi.single_apply] using a j g⟩
 have ⟨E1,f1,g1,h1⟩:=E 1;have ⟨E2,f2,g2,h2⟩:=E 2;have ⟨E3,f3,g3,h3⟩:=E 3;have u1:=P E1 f1 g1;have u2:=P E2 f2 g2;have u3:=P E3 f3 g3;have v1:=Q E1 f1 g1;have v2:=Q E2 f2 g2;have v3:=Q E3 f3 g3;have w1:=R E1 f1 g1;have w2:=R E2 f2 g2;have w3:=R E3 f3 g3;simp [h1,h2,h3] at u1 u2 u3 v1 v2 v3 w1 w2 w3;have F:∀ c:Fin 4,c≠0->Y1 (1,c)≠0->Y2 (2,c)≠0->Y3 (3,c)≠0->False:=λ c h u v w=>K8 hD h λ x y z=>⟨(x/Y1 (1,c))•Y1+(y/Y2 (2,c))•Y2+(z/Y3 (3,c))•Y3,add_mem (add_mem (L.smul_mem _ a1) (L.smul_mem _ a2)) (L.smul_mem _ a3),λ i=>by simp [c1,c2,c3],by simp [d2,d3,u],by simp [d1,e3,v],by simp [e1,e2,w]⟩;have:=F 1 (by simp);have:=F 2 (by simp);have:=F 3 (by simp);grind
theorem wr {L:Submodule KD ze} (hL:zg L) (h6:Module.finrank KD L=6) (hr:Module.finrank KD (L.map (z9 0))=3) (hc:Module.finrank KD (L.map (zD 0))=3) (hd0:Module.finrank KD (zm L 0 0)=0):False:=by
 have hD:=K3 hL h6 hr hc hd0;by_cases h:∃ R:Fin 4,R≠0/\finrank KD ((zC L 0).map (z9 R))=2
 . have ⟨R,hR,h2⟩:=h;have ⟨Z,hK⟩:=JX hD h2;have ⟨c,hc,pc⟩:=Kq hD hR hK;exact KA (kp hD (p:=Equiv.swap 1 R) (q:=Equiv.swap 1 c) (jU (by simp) hR.symm) (jU (by simp) hc.symm)) (wZ (jU (by simp) hc.symm) (by rwa [Equiv.swap_apply_left])) λ i j h=>by simpa [y9] using pc _ _ λ e=>h (by simpa using congrArg (Equiv.swap 1 c) e)
 . exact KB hD λ R a=>by have:=JW hD a;have:=not_and.1 (not_exists.1 h R) a;omega
end
section
open Module Submodule LinearMap
abbrev qK (L:Submodule KD ze):=zh L 0
def kr (L:Submodule KD ze):Prop:=zg L/\finrank KD L=6/\finrank KD (L.map (z9 0))=3/\finrank KD (L.map (zD 0))=3/\finrank KD (zm L 0 0)=1
theorem jM {L:Submodule KD ze} {X}:X∈qK L↔X∈L/\∀ j,X (0,j)=0:=by simp [zh,funext_iff,zA]
theorem ws {L:Submodule KD ze} {H} (h:H∈qK L):(∀ j,H (0,j)=0)/\zw H=0/\zB H=![H (1,0),H (2,0),H (3,0)]/\zv H=![![H (1,1),H (1,2),H (1,3)],![H (2,1),H (2,2),H (2,3)],![H (3,1),H (3,2),H (3,3)]]:=by
 have h0:=(jM.1 h).2;refine ⟨h0,funext λ b=>by simp [qw,h0],funext λ a=>?_,funext λ a=>funext λ b=>?_⟩<;>fin_cases a<;>try fin_cases b
 all_goals simp [qn,zv,h0]
theorem W0 {L} (H:kr L):kr (L.map (zM:ze→ₗ[KD]ze)):=by
 have ⟨hL,h6,hr,hc,hd⟩:=H;have e:∀ f g:ze→ₗ[KD]Fin 4->KD,f.comp (zM:ze→ₗ[KD]ze)=g->(L.map (zM:ze→ₗ[KD]ze)).map f=L.map g:=λ f g h=>by rw [←Submodule.map_comp,h]
 exact ⟨zX hL,(zT L).trans h6,by rw [e _ (zD 0) (LinearMap.ext λ X=>funext λ j=>rfl)];exact hc,by rw [e _ (z9 0) (LinearMap.ext λ X=>funext λ j=>rfl)];exact hr,by rw [ja,LinearEquiv.finrank_map_eq];exact hd⟩
theorem W4 {L} (H:kr L) (σ τ:Equiv.Perm (Fin 3)) {T} (hT:T∈zm L 0 0):∃ L' T',kr L'/\T'∈zm L' 0 0/\∀ a b,z7 0 0 T' a b=z7 0 0 T (σ a) (τ b):=by
 have ⟨hL,h6,hr,hc,hd⟩:=H;let p:=Equiv.Perm.decomposeFin.symm (0,σ);let q:=Equiv.Perm.decomposeFin.symm (0,τ);have p0:p 0=0:=Equiv.Perm.decomposeFin_symm_apply_zero _ _;have q0:q 0=0:=Equiv.Perm.decomposeFin_symm_apply_zero _ _;let R:ze→ₗ[KD]ze:=(zq p q:ze→ₗ[KD]ze);have m:∀ (f:ze→ₗ[KD]Fin 4->KD) (e:(Fin 4->KD)≃ₗ[KD](Fin 4->KD)),f.comp R=(e:(Fin 4->KD)→ₗ[KD](Fin 4->KD)).comp f->finrank KD ((L.map R).map f)=finrank KD (L.map f):=λ f e h=>by rw [←Submodule.map_comp,h,Submodule.map_comp,LinearEquiv.finrank_map_eq]
 have I:zm (L.map R) 0 0=(zm L 0 0).map R:=by
  ext Y;constructor
  . intro h;obtain ⟨⟨X,hX,rfl⟩,a,b⟩:=qJ h;exact ⟨X,yc hX (λ j=>by simpa [R,zy,p0] using a (q.symm j)) (λ i=>by simpa [R,zy,q0] using b (p.symm i)),rfl⟩
  . rintro ⟨X,h,rfl⟩;have ⟨h,a,b⟩:=qJ h;exact yc ⟨X,h,rfl⟩ (λ j=>by simp [R,zy,p0,a]) (λ i=>by simp [R,zy,q0,b])
 refine ⟨_,R T,⟨zH hL p q,(zF L p q).trans h6,?_,?_,by rw [I,LinearEquiv.finrank_map_eq];exact hd⟩,I▸⟨T,hT,rfl⟩,λ a b=>by simp [qL,R,zy,p,q,Equiv.Perm.decomposeFin_symm_apply_succ]⟩
 . rw [m _ (LinearEquiv.funCongrLeft KD KD q) (LinearMap.ext λ X=>funext λ j=>by simp [R,zA,zy,p0])];exact hr
 . rw [m _ (LinearEquiv.funCongrLeft KD KD p) (LinearMap.ext λ X=>funext λ j=>by simp [R,qF,zy,q0])];exact hc
theorem W5 {L} (H:kr L):∃ f g:Fin 3->KD,f≠0/\g≠0/\(∀ Y∈L,∑ k,f k*zw Y k=∑ k,g k*zB Y k)/\∀ x y,∑ k,f k*x k=∑ k,g k*y k->∃ Y∈L,zw Y=x/\zB Y=y:=by
 have ⟨hL,h6,hr,hc,hd⟩:=H;obtain ⟨-,hx,hy,-,e⟩:=ym hL h6 hr hc;have h5:finrank KD (L.map qT)=5:=by omega
 have ⟨φ,hφ,hle⟩:=(L.map qT).exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 λ h=>by rw [h,finrank_top] at h5;simp at h5);have hW:=eq_of_le_of_finrank_le hle (by have:=jA φ hφ;simp at this;omega);have F:∀ x y,φ (x,y)=∑ k,φ (Pi.single k 1,0)*x k-∑ k,-φ (0,Pi.single k 1)*y k:=λ x y=>by
  rw [show (x,y)=x 0•(Pi.single 0 1,0)+x 1•(Pi.single 1 1,0)+x 2•(Pi.single 2 1,0)+y 0•(0,Pi.single 0 1)+y 1•(0,Pi.single 1 1)+y 2•(0,Pi.single 2 1) by ext k<;>fin_cases k<;>simp];simp only [map_add,map_smul,smul_eq_mul,Fin.sum_univ_three];ring
 have M:∀ x y,(x,y)∈L.map qT↔∑ k,φ (Pi.single k 1,0)*x k=∑ k,-φ (0,Pi.single k 1)*y k:=λ x y=>by rw [hW,mem_ker,F,sub_eq_zero]
 refine ⟨_,_,λ h=>hφ ?_,λ h=>hφ ?_,λ Y h=>(M _ _).1 ⟨Y,h,rfl⟩,λ x y h=>?_⟩
 . refine LinearMap.ext λ ⟨x,y⟩=>?_;have ⟨Y,a,b⟩:=hy y;have:=(M _ _).1 ⟨Y,a,rfl⟩;simp only [funext_iff,Pi.zero_apply] at h;simp [h,b] at this;rw [F];simp [h,this]
 . refine LinearMap.ext λ ⟨x,y⟩=>?_;have ⟨Y,a,b⟩:=hx x;have:=(M _ _).1 ⟨Y,a,rfl⟩;simp only [funext_iff,Pi.zero_apply] at h;simp [h,b] at this;rw [F];simp [h,this]
 . have ⟨Y,a,b⟩:=(M x y).2 h;exact ⟨Y,a,congrArg Prod.fst b,congrArg Prod.snd b⟩
theorem Zn {L:Submodule KD ze} (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) {X Y:ze} (a:X∈qK L) (b:Y∈qK L) (hli:∀ u v:KD,u•X+v•Y=0->u=0/\v=0) (ρ:Fin 4) (c:∀ j,X (ρ,j)=0) (d:∀ j,Y (ρ,j)=0):finrank KD ((qK L).map (z9 ρ))≤1:=by
 refine jC h6 hr (W:=span KD (Set.range ![X,Y])) ?_ ?_ ρ ?_
 . rw [span_le];rintro _ ⟨k,rfl⟩;fin_cases k;exacts [a,b]
 . rw [finrank_span_eq_card (LinearIndependent.pair_iff.2 hli)];simp
 . intro Z h j;obtain ⟨w,rfl⟩:=(mem_span_range_iff_exists_fun KD).1 h;simp [Fin.sum_univ_two,c,d]
def k4 (P v x:Fin 3->KD):KD:=x 0*(P 1*v 2+P 2*v 1)+x 1*(P 0*v 2+P 2*v 0)+x 2*(P 0*v 1+P 1*v 0)
theorem Qh {P v:Fin 3->KD} (hP:P 0*P 1*P 2≠0) (h:∀ b,k4 P v (Pi.single b 1)=0):v=0:=by
 have a:=h 0;have b:=h 1;have c:=h 2;simp [k4] at a b c;funext k;fin_cases k<;>simp<;>grind
theorem W6 {L} (H:kr L) (hF:yx) {T:ze} (hT:T∈zm L 0 0) (h0:∀ a,a≠0->∀ b,z7 0 0 T a b=0) (hn:∀ b,z7 0 0 T 0 b≠0):False:=by
 have ⟨hL,h6,hr,hc,hd⟩:=H;obtain ⟨-,-,t0⟩:=qJ hT;obtain ⟨P,hP⟩:∃ P:Fin 3->KD,∀ b,z7 0 0 T 0 b=P b:=⟨_,λ _=>rfl⟩;have hp:P 0*P 1*P 2≠0:=by simp only [←hP];exact mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)
 have hE:∀ Y∈L,zB Y 1*k4 P (zv Y 2) (zw Y)+zB Y 2*k4 P (zv Y 1) (zw Y)=0:=λ Y h=>by
  have:=(qG hL h hT).2;have a:=h0 1 (by simp);have b:=h0 2 (by simp);simp [zE,zR,Fin.sum_univ_three,z6,a,b,hP] at this;simp only [k4];grind
 obtain ⟨f,g,f0,g0,-,hl⟩:=W5 ⟨hL,h6,hr,hc,hd⟩;have mk:∀ y:Fin 3->KD,∑ k,g k*y k=0->∃ H∈qK L,zB H=y:=λ y h=>by obtain ⟨H,a,b,rfl⟩:=hl 0 y (by simp [h]);exact ⟨H,jM.2 ⟨a,jl hL a b⟩,rfl⟩
 have hTz:∀ a:Fin 3,a≠0->∀ j,T (a.succ,j)=0:=λ a h j=>Fin.cases (t0 _) (λ b=>by have:=h0 a h b;rwa [qL] at this) j;have h11:T (1,1)≠0:=by have:=hn 0;rwa [qL] at this
 have ind:∀ X:ze,∀ a:Fin 3,X (a.succ,0)=1->∀ u v:KD,u•T+v•X=0->u=0/\v=0:=λ X a h u v e=>by
  have p:=congrFun e (a.succ,0);have q:=congrFun e (1,1);simp [t0,h] at p;subst p;simp at q;exact ⟨q.resolve_right h11,rfl⟩
 have fin:∀ X Y:ze,X∈qK L->Y∈qK L->(∃ a:Fin 3,X (a.succ,0)=1)->(∃ a:Fin 3,Y (a.succ,0)=1)->(∀ j,X (2,j)=0)->(∀ j,Y (3,j)=0)->False:=λ X Y a b ⟨i,c⟩ ⟨k,d⟩ e f=>hF L hL h6 hr 2 3 (by simp) (by simp) (by simp) (Zn h6 hr hT.1 a (ind X i c) 2 (hTz 1 (by simp)) e) (Zn h6 hr hT.1 b (ind Y k d) 3 (hTz 2 (by simp)) f);have pol:∀ X∈qK L,∀ Y∈L,zB Y 1*k4 P (zv X 2) (zw Y)+zB Y 2*k4 P (zv X 1) (zw Y)+zB X 1*k4 P (zv Y 2) (zw Y)+zB X 2*k4 P (zv Y 1) (zw Y)=0/\zB X 1*k4 P (zv X 2) (zw Y)+zB X 2*k4 P (zv X 1) (zw Y)=0:=λ X a Y b=>by
  have p:=hE _ (add_mem b a.1);have q:=hE _ (sub_mem b a.1);have r:=hE Y b;simp only [map_add,map_sub,(ws a).2.1,Pi.zero_apply,add_zero,sub_zero,Pi.add_apply,Pi.sub_apply,yO,jm,k4] at p q r ⊢;exact ⟨by grind,by grind⟩
 by_cases g0':g 0=0
 . have ⟨X,a,e⟩:=mk (Pi.single 0 1) (by rw [qQ,g0',zero_mul]);have K:=ws a;rw [K.2.2.1] at e;have e0:=congrFun e 0;have e1:=congrFun e 1;have e2:=congrFun e 2;simp at e0 e1 e2;obtain ⟨k,hk⟩:∃ k,f k≠0:=by by_contra h;push Not at h;exact f0 (funext h)
   obtain ⟨k',hk'⟩:∃ k,g k≠0:=by by_contra h;push Not at h;exact g0 (funext h)
   have z:=qC (LinearMap.mk₂ KD (λ x y:Fin 3->KD=>y 1*k4 P (zv X 2) x+y 2*k4 P (zv X 1) x) (by intros;simp only [k4,Pi.add_apply];ring) (by intros;simp only [k4,Pi.smul_apply,smul_eq_mul];ring) (by intros;simp only [k4,Pi.add_apply];ring) (by intros;simp only [k4,Pi.smul_apply,smul_eq_mul];ring)) (qf f) (qf g) (x0:=Pi.single k (f k)⁻¹) (y0:=Pi.single k' (g k')⁻¹) (by simp [qf,qQ,hk]) (by simp [qf,qQ,hk']) λ x y e=>by
    obtain ⟨Y,b,rfl,rfl⟩:=hl x y e;have:=(pol X a Y b).1;rw [K.2.2.1] at this;simp [e1,e2] at this;simp only [mk₂_apply];grind
   have u:=Qh hp λ b=>by simpa using z (Pi.single b 1) (Pi.single 1 1)
   have v:=Qh hp λ b=>by simpa using z (Pi.single b 1) (Pi.single 2 1)
   rw [K.2.2.2] at u v;have u:=congrFun u;have v:=congrFun v;simp [Fin.forall_fin_succ] at u v;exact fin X X a a ⟨0,e0⟩ ⟨0,e0⟩ (λ j=>by fin_cases j<;>simp [e1,v]) λ j=>by fin_cases j<;>simp [e2,u]
 . have ⟨U,a,eu⟩:=mk ![-(g 1/g 0),1,0] (by simp [Fin.sum_univ_three];field_simp;ring);have ⟨W,b,ew⟩:=mk ![-(g 2/g 0),0,1] (by simp [Fin.sum_univ_three];field_simp;ring);have t:∀ X∈qK L,∀ b,zB X 1*zv X 2 b+zB X 2*zv X 1 b=0:=λ X h=>congrFun (Qh (v:=λ b=>zB X 1*zv X 2 b+zB X 2*zv X 1 b) hp λ b=>by have ⟨Y,c,d⟩:=qz hL hr (Pi.single b 1);have:=(pol X h Y c).2;rw [d] at this;simp only [k4] at this ⊢;grind);have tu:=t U a;have tw:=t W b;have U':=ws a;have W':=ws b;rw [U'.2.2.1] at eu;rw [U'.2.2.1,U'.2.2.2] at tu;rw [W'.2.2.1] at ew;rw [W'.2.2.1,W'.2.2.2] at tw;have u0:=congrFun eu 0;have u1:=congrFun eu 1;have u2:=congrFun eu 2;have w0:=congrFun ew 0;have w1:=congrFun ew 1;have w2:=congrFun ew 2;simp at u0 u1 u2 w0 w1 w2;simp [Fin.forall_fin_succ,u1,u2,w1,w2] at tu tw;exact fin W U b a ⟨2,w2⟩ ⟨1,u1⟩ (λ j=>by fin_cases j;exacts [w1,tw.1,tw.2.1,tw.2.2]) λ j=>by fin_cases j;exacts [u2,tu.1,tu.2.1,tu.2.2]
def yZ (p q:KD):ze:=λ x=>![![0,0,0,0],![0,0,0,0],![0,0,1,p],![0,0,q,-(p*q)]] x.1 x.2
def W7 (p q:KD) (x y:Fin 3->KD) (A:zx):KD:=y 0*x 0*(-(p*q)*A 1 1+q*A 1 2+p*A 2 1+A 2 2)+y 0*(x 1*(p*A 2 0-p*q*A 1 0)+x 2*(A 2 0+q*A 1 0))+x 0*(y 1*(-(p*q)*A 0 1+q*A 0 2)+y 2*(p*A 0 1+A 0 2))+A 0 0*(y 1*(-(p*q)*x 1+q*x 2)+y 2*(p*x 1+x 2))
theorem vX {L} (hL:zg L) {p q} (hT:yZ p q∈zm L 0 0) {Y} (h:Y∈L):W7 p q (zw Y) (zB Y) (zv Y)=0:=by
 have:=(qG hL h hT).2;simp [zE,zR,Fin.sum_univ_three,z6,qL,yZ] at this;simp only [W7];grind
theorem Ku {L} (hd:finrank KD (zm L 0 0)=1) {T} (hT:T∈zm L 0 0) (h0:T≠0) (S) (hS:S∈zm L 0 0):∃ c:KD,S=c•T:=by
 rw [(eq_of_le_of_finrank_le ((span_singleton_le_iff_mem _ _).2 hT) (by rw [hd,finrank_span_singleton h0])).symm,mem_span_singleton] at hS;obtain ⟨c,rfl⟩:=hS;exact ⟨c,rfl⟩
theorem Qi {L} (hL:zg L) (hr:finrank KD (L.map (z9 0))=3) {l:(Fin 4->KD)→ₗ[KD]KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (j:Fin 4):∃ M:ze,∀ H∈qK L,zo (z7 0 j (M+H))=24*l (Pi.single j 1)^4:=by
 have ⟨a,T,hT,v⟩:=(qu hL hr).1 (Pi.single j 1);refine ⟨λ x=>a+T x,λ H h=>?_⟩;have e:=qP hL (add_mem hT h.1) a;rw [yd _ 0] at e;have w:∀ k,a+(T+H) (0,k)=(Pi.single j (1:KD):Fin 4->KD) k:=λ k=>by rw [Pi.add_apply,(jM.1 h).2,add_zero,congrFun v k]
 simp only [w,Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at e;rw [show l (Pi.single j 1)=a by rw [v];exact hl a T hT,←e];congr 1;funext c d;simp only [zt,Pi.add_apply];ring
theorem W8 (M B:zx) (c:KD) (h:∀ s:KD,zo (M+s•B)=c):zo B=0/\qm B M=0/\qm M B=0:=by
 obtain ⟨-,a,b,d⟩:=qE (zo M-c) (qm M B) (qm B M) (zo B) λ s=>by have:=ji 1 s M B;rw [show (λ i j=>1*M i j+s*B i j)=M+s•B by funext i j;simp,h s] at this;grind
 exact ⟨d,b,a⟩
theorem ks {L} (hL:zg L) (hr:finrank KD (L.map (z9 0))=3) {H} (h:H∈qK L):H (1,1)*(H (2,2)*H (3,3)+H (2,3)*H (3,2))+H (1,2)*(H (2,1)*H (3,3)+H (2,3)*H (3,1))+H (1,3)*(H (2,1)*H (3,2)+H (2,2)*H (3,1))=0/\H (1,0)*(H (2,2)*H (3,3)+H (2,3)*H (3,2))+H (1,2)*(H (2,0)*H (3,3)+H (2,3)*H (3,0))+H (1,3)*(H (2,0)*H (3,2)+H (2,2)*H (3,0))=0/\H (1,0)*(H (2,1)*H (3,3)+H (2,3)*H (3,1))+H (1,1)*(H (2,0)*H (3,3)+H (2,3)*H (3,0))+H (1,3)*(H (2,0)*H (3,1)+H (2,1)*H (3,0))=0/\H (1,0)*(H (2,1)*H (3,2)+H (2,2)*H (3,1))+H (1,1)*(H (2,0)*H (3,2)+H (2,2)*H (3,0))+H (1,2)*(H (2,0)*H (3,1)+H (2,1)*H (3,0))=0:=by
 obtain ⟨l,hl,-⟩:=(qu hL hr).2;have t:∀ j,zo (z7 0 j H)=0:=λ j=>by have ⟨M,hM⟩:=Qi hL hr hl j;exact (W8 (z7 0 j M) (z7 0 j H) _ λ s=>by rw [←map_smul,←map_add];exact hM _ (smul_mem _ s h)).1
 have a:=t 0;have b:=t 1;have c:=t 2;have d:=t 3;rw [zs] at a b c d;exact ⟨a,b,c,d⟩
theorem Qj {L} (hL:zg L) (h6:finrank KD L=6) (hr:finrank KD (L.map (z9 0))=3) {l:(Fin 4->KD)→ₗ[KD]KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) {j:Fin 4} (hj:l (Pi.single j 1)≠0):∃ B:zx,zo B≠0/\(∀ H∈qK L,zo (B+z7 0 j H)=zo B)/\finrank KD ((qK L).map (z7 0 j))=3:=by
 have ⟨M,hM⟩:=Qi hL hr hl j;have hB:=hM 0 (zero_mem _);rw [add_zero] at hB;refine ⟨z7 0 j M,by rw [hB];exact mul_ne_zero (by norm_num) (pow_ne_zero _ hj),λ H h=>by rw [←map_add,hM H h,hB],?_⟩;have e:=zW (z7 0 j) (qK L);rw [qs hL h6 hr hl hj,finrank_bot,add_zero,y5 h6 hr] at e;exact e
theorem W9 (w0 w1 w2:KD) (hz:w0=0\/w1=0\/w2=0) (hw:w0≠0\/w1≠0\/w2≠0):∃ n0 n1 n2:KD,(n0≠0\/n1≠0\/n2≠0)/\n0*n1*n2=0/\w2*n1+w1*n2=0/\w2*n0+w0*n2=0/\w1*n0+w0*n1=0:=by
 rcases hz with h|h|h<;>subst h;exacts [⟨0,w1,-w2,by grind,by ring,by ring,by ring,by ring⟩,⟨w0,0,-w2,by grind,by ring,by ring,by ring,by ring⟩,⟨w0,-w1,0,by grind,by ring,by ring,by ring,by ring⟩]
theorem K9 (B:zx) (N:Submodule KD zx) (h3:finrank KD N=3) (h0:∀ T∈N,∀ b,T 0 b=0) (hB:zo B≠0) (hN:∀ T∈N,zo (B+T)=zo B):∃ n0 n1 n2:KD,(n0≠0\/n1≠0\/n2≠0)/\n0*n1*n2=0/\(λ a b=>if a=1 then ![n0,n1,n2] b else 0)∈N/\(λ a b=>if a=2 then ![n0,n1,n2] b else 0)∈N:=by
 have ⟨z,r⟩:=jH B N h3 h0 hB hN;have ⟨n0,n1,n2,a,b,c,d,e⟩:=W9 _ _ _ z (by by_contra h;push Not at h;apply hB;rw [zs,h.1,h.2.1,h.2.2];ring);exact ⟨n0,n1,n2,a,b,r ![n0,n1,n2] (by simpa using c) (by simpa using d) (by simpa using e)⟩
theorem Ka (B:zx) (N:Submodule KD zx) (h3:finrank KD N=3) (h0:∀ T∈N,∀ b,T b 0=0) (hB:zo B≠0) (hN:∀ T∈N,zo (B+T)=zo B):∃ n0 n1 n2:KD,(n0≠0\/n1≠0\/n2≠0)/\n0*n1*n2=0/\(λ a b=>if b=1 then ![n0,n1,n2] a else 0)∈N/\(λ a b=>if b=2 then ![n0,n1,n2] a else 0)∈N:=by
 have ⟨z,r⟩:=jO B N h3 h0 hB hN;have ⟨n0,n1,n2,a,b,c,d,e⟩:=W9 _ _ _ z (by by_contra h;push Not at h;apply hB;rw [zs,h.1,h.2.1,h.2.2];ring);exact ⟨n0,n1,n2,a,b,r ![n0,n1,n2] (by simpa using c) (by simpa using d) (by simpa using e)⟩
theorem Wa {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hT:yZ p q∈zm L 0 0) {l:(Fin 4->KD)→ₗ[KD]KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) {j:Fin 4} (hj:l (Pi.single j 1)≠0) (hR:∀ X∈qK L,∀ k,X (1,k)=0):False:=by
 obtain ⟨hL,h6,hr,-,-⟩:=H;have ⟨B,hB,hN,h3⟩:=Qj hL h6 hr hl hj;have ⟨n0,n1,n2,hn,hnp,⟨Z,hZ,e1⟩,⟨W,hW,e2⟩⟩:=K9 B _ h3 (λ X ⟨Y,h,e⟩ b=>by rw [←e,zt];exact hR Y h _) hB λ X ⟨Y,h,e⟩=>e▸hN Y h;have Q:=λ t z w:KD=>qb hL (jM.1 (add_mem (add_mem (smul_mem _ t hT.1) (smul_mem _ z hZ)) (smul_mem _ w hW))).1;have ez:∀ a b,Z (z8 0 a,z8 j b)=if a=1 then ![n0,n1,n2] b else 0:=λ a b=>by have:=congrFun (congrFun e1 a) b;rwa [zt] at this
 have ew:∀ a b,W (z8 0 a,z8 j b)=if a=2 then ![n0,n1,n2] b else 0:=λ a b=>by have:=congrFun (congrFun e2 a) b;rwa [zt] at this
 have Q1:=Q 0 1 0;have Q2:=Q 0 0 1;have Q3:=Q 0 1 1;have Q4:=Q 1 1 0;have Q5:=Q 1 0 1;have Q6:=Q 1 0 0;have z0:=(jM.1 hZ).2;have w0:=(jM.1 hW).2;have z1:=hR Z hZ;have w1:=hR W hW;clear Q hN e1 e2 hR;fin_cases j;all_goals
  have a:=ez 1 0;have b:=ez 1 1;have c:=ez 1 2;have d:=ez 2 0;have e:=ez 2 1;have f:=ez 2 2;have g:=ew 1 0;have h:=ew 1 1;have i:=ew 1 2;have k:=ew 2 0;have m:=ew 2 1;have o:=ew 2 2;simp [z8] at a b c d e f g h i k m o;simp [qY,yl,Fintype.sum_prod_type,Fin.sum_univ_four,yZ,a,b,c,d,e,f,g,h,i,k,m,o,z0,w0,z1,w1] at Q1 Q2 Q3 Q4 Q5 Q6;clear ez ew;rcases eq_or_ne (n0+n1+n2) 0 with s|s<;>grind
theorem Kb (K:Submodule KD ze) (hK:finrank KD K=3) {u v w:ze} (a:u∈K) (b:v∈K) (c:w∈K) (h:∀ x y z:KD,x•u+y•v+z•w=0->x=0/\y=0/\z=0) (X) (hX:X∈K):∃ x y z:KD,X=x•u+y•v+z•w:=by
 have l:LinearIndependent KD ![u,v,w]:=by rw [Fintype.linearIndependent_iff];intro g e;simp [Fin.sum_univ_three] at e;have ⟨x,y,z⟩:=h _ _ _ e;intro i;fin_cases i<;>assumption
 have e:span KD (Set.range ![u,v,w])=K:=eq_of_le_of_finrank_le (span_le.2 λ _ ⟨k,e⟩=>by fin_cases k<;>simp_all) (by rw [hK,finrank_span_eq_card l];simp);rw [←e] at hX;obtain ⟨g,rfl⟩:=(mem_span_range_iff_exists_fun KD).1 hX;exact ⟨g 0,g 1,g 2,by simp [Fin.sum_univ_three]⟩
theorem Wb {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {l:(Fin 4->KD)→ₗ[KD]KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (hj:l (Pi.single 0 1)≠0) (hC:∀ X∈qK L,∀ i,X (i,1)=0):False:=by
 obtain ⟨hL,h6,hr,-,hd⟩:=id H;have ⟨B,hB,hN,h3⟩:=Qj hL h6 hr hl hj;have ⟨n0,n1,n2,hn,hnp,⟨Z,hZ,e1⟩,⟨W,hW,e2⟩⟩:=Ka B _ h3 (λ X ⟨Y,h,e⟩ a=>by rw [←e,zt];exact hC Y h _) hB λ X ⟨Y,h,e⟩=>e▸hN Y h;have ez:∀ a b,Z (z8 0 a,z8 0 b)=if b=1 then ![n0,n1,n2] a else 0:=λ a b=>by have:=congrFun (congrFun e1 a) b;rwa [zt] at this
 have ew:∀ a b,W (z8 0 a,z8 0 b)=if b=2 then ![n0,n1,n2] a else 0:=λ a b=>by have:=congrFun (congrFun e2 a) b;rwa [zt] at this
 have M:∀ t z w:KD,t•yZ p q+z•Z+w•W∈qK L:=λ t z w=>add_mem (add_mem (smul_mem _ t hT.1) (smul_mem _ z hZ)) (smul_mem _ w hW);have z0:=(jM.1 hZ).2;have w0:=(jM.1 hW).2;have zc:=hC Z hZ;have wc:=hC W hW;have a:=ez 0 1;have b:=ez 1 1;have c:=ez 2 1;have d:=ez 0 2;have e:=ez 1 2;have f:=ez 2 2;have g:=ew 0 1;have h:=ew 1 1;have i:=ew 2 1;have k:=ew 0 2;have m:=ew 1 2;have o:=ew 2 2;simp [z8] at a b c d e f g h i k m o;have i3:∀ x y z:KD,x•yZ p q+y•Z+z•W=0->x=0/\y=0/\z=0:=λ x y z u=>by
  have:=congrFun u (1,2);have:=congrFun u (2,2);have:=congrFun u (3,2);have:=congrFun u (1,3);have:=congrFun u (2,3);have:=congrFun u (3,3);simp [yZ,a,b,c,d,e,f,g,h,i,k,m,o] at *;grind
 have ab:∀ μ ν:KD,μ*Z (1,0)+ν*W (1,0)=0->μ*Z (2,0)+ν*W (2,0)=0->μ*Z (3,0)+ν*W (3,0)=0->μ=0/\ν=0:=λ μ ν x y z=>by
  have u:=add_mem (smul_mem _ μ hZ) (smul_mem _ ν hW);have ⟨c,e⟩:=Ku hd hT (λ h=>by have:=congrFun h (2,2);simp [yZ] at this) _ (yc u.1 (jM.1 u).2 λ i=>by fin_cases i<;>simp [z0,w0,x,y,z]);have:=i3 (-c) μ ν (by rw [add_assoc,e,neg_smul,neg_add_cancel]);exact ⟨this.2.1,this.2.2⟩
 have G:=λ t z w=>(ks hL hr (M t z w)).2.1;have P:=λ t z w=>qb hL (jM.1 (M t z w)).1;have g1:=G 0 1 1;have g2:=G 0 1 (-1);have g3:=G 1 1 0;have g4:=G 1 0 1;have p1:=P 0 1 0;have p2:=P 0 0 1;simp [yZ,a,b,c,d,e,f,g,h,i,k,m,o] at g1 g2 g3 g4;simp [qY,yl,Fintype.sum_prod_type,Fin.sum_univ_four,a,b,c,d,e,f,g,h,i,k,m,o,z0,w0,zc,wc] at p1 p2;have:=ab 1 0;have:=ab 0 1;have:=ab (W (1,0)) (-Z (1,0));have:=ab (W (2,0)) (-Z (2,0));have:=ab (W (3,0)) (-Z (3,0));have:Z (1,0)*n1*n2+Z (2,0)*n0*n2+Z (3,0)*n0*n1=0:=by grind
 have:W (1,0)*n1*n2+W (2,0)*n0*n2+W (3,0)*n0*n1=0:=by grind
 have:(n0+n1+n2)*(Z (1,0)+Z (2,0)+Z (3,0))-(Z (1,0)*n0+Z (2,0)*n1+Z (3,0)*n2)=0:=by grind
 have:(n0+n1+n2)*(W (1,0)+W (2,0)+W (3,0))-(W (1,0)*n0+W (2,0)*n1+W (3,0)*n2)=0:=by grind
 have r:n0=0/\Z (1,0)=0/\W (1,0)=0:=by clear G P M ab i3 ez ew g1 g2 p1 p2;rcases eq_or_ne n0 0 with u|u<;>rcases eq_or_ne n1 0 with v|v<;>rcases eq_or_ne n2 0 with w|w<;>grind
 refine Wa H hp hq hT hl hj λ X x k=>?_;obtain ⟨u,v,w,rfl⟩:=Kb _ (y5 h6 hr) hT.1 hZ hW i3 X x;fin_cases k<;>simp [yZ,r,a,d,g,k,zc,wc]
def vY (x0 x1 x2 y0 y1 y2 z0 z1 z2:KD):KD:=x0*(y1*z2-y2*z1)-x1*(y0*z2-y2*z0)+x2*(y0*z1-y1*z0)
theorem Wc {x0 x1 x2 y0 y1 y2 z0 z1 z2:KD} (h:vY x0 x1 x2 y0 y1 y2 z0 z1 z2≠0) (r0 r1 r2:KD):∃ a b c:KD,a*x0+b*y0+c*z0=r0/\a*x1+b*y1+c*z1=r1/\a*x2+b*y2+c*z2=r2:=by
 refine ⟨vY r0 r1 r2 y0 y1 y2 z0 z1 z2/vY x0 x1 x2 y0 y1 y2 z0 z1 z2,vY x0 x1 x2 r0 r1 r2 z0 z1 z2/vY x0 x1 x2 y0 y1 y2 z0 z1 z2,vY x0 x1 x2 y0 y1 y2 r0 r1 r2/vY x0 x1 x2 y0 y1 y2 z0 z1 z2,?_,?_,?_⟩<;>field_simp<;>simp only [vY]<;>ring
theorem Wd {B:zx} {N:Submodule KD zx} (hB:zo B≠0) (hN:∀ X∈N,zo (B+X)=zo B) {X Y Z:zx} (hX:X∈N) (hY:Y∈N) (hZ:Z∈N) (a:Fin 3):vY (X a 0) (X a 1) (X a 2) (Y a 0) (Y a 1) (Y a 2) (Z a 0) (Z a 1) (Z a 2)=0/\vY (X 0 a) (X 1 a) (X 2 a) (Y 0 a) (Y 1 a) (Y 2 a) (Z 0 a) (Z 1 a) (Z 2 a)=0:=by
 constructor<;>by_contra h
 . have ⟨c1,c2,c3,e0,e1,e2⟩:=Wc h (-B a 0) (-B a 1) (-B a 2);have:=hN _ (add_mem (add_mem (smul_mem _ c1 hX) (smul_mem _ c2 hY)) (smul_mem _ c3 hZ));rw [jb _ a,Fin.sum_univ_three] at this;simp at this;apply hB;rw [←this];grind
 . have ⟨c1,c2,c3,e0,e1,e2⟩:=Wc h (-B 0 a) (-B 1 a) (-B 2 a);have:=hN _ (add_mem (add_mem (smul_mem _ c1 hX) (smul_mem _ c2 hY)) (smul_mem _ c3 hZ));rw [jc _ a,Fin.sum_univ_three] at this;simp at this;apply hB;rw [←this];grind
theorem Kc {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {f:Fin 3->KD} {g0:KD} (hg:g0≠0) (hrel:∀ Y∈L,∑ k,f k*zw Y k=g0*zB Y 0) (hlift:∀ x y,∑ k,f k*x k=g0*y 0->∃ Y∈L,zw Y=x/\zB Y=y):∃ U W:ze,U∈qK L/\W∈qK L/\U (1,0)=0/\U (2,0)=1/\U (3,0)=0/\W (1,0)=0/\W (2,0)=0/\W (3,0)=1/\((∀ X∈qK L,∀ j,X (1,j)=0)\/∃ κ:KD,κ≠0/\∀ X∈qK L,(∀ i,X (i,1)=0)/\X (1,2)=κ*(q*X (2,0)+X (3,0))/\X (1,3)=κ*p*(q*X (2,0)-X (3,0))):=by
 obtain ⟨hL,-,hr,-,hd⟩:=H;have y0:∀ X∈qK L,X (1,0)=0:=λ X h=>by have:=hrel X h.1;obtain ⟨-,a,b,-⟩:=ws h;rw [a,b] at this;simpa [hg] using this
 have mk:∀ y:Fin 3->KD,y 0=0->∃ X∈qK L,zB X=y:=λ y h=>by obtain ⟨X,a,b,rfl⟩:=hlift 0 y (by simp [h]);exact ⟨X,jM.2 ⟨a,jl hL a b⟩,rfl⟩
 have ⟨U,hU,eu⟩:=mk (Pi.single 1 1) (by simp);have ⟨W,hW,ew⟩:=mk (Pi.single 2 1) (by simp);rw [(ws hU).2.2.1] at eu;rw [(ws hW).2.2.1] at ew;have u1:=congrFun eu 0;have u2:=congrFun eu 1;have u3:=congrFun eu 2;have w1:=congrFun ew 0;have w2:=congrFun ew 1;have w3:=congrFun ew 2;simp at u1 u2 u3 w1 w2 w3;have dec:∀ X∈qK L,∃ t:KD,∀ i j,X (i,j)=t*yZ p q (i,j)+X (2,0)*U (i,j)+X (3,0)*W (i,j):=λ X h=>by
  have Z:=sub_mem (sub_mem h (smul_mem _ (X (2,0)) hU)) (smul_mem _ (X (3,0)) hW);have ⟨t,e⟩:=Ku hd hT (λ h=>by have:=congrFun h (2,2);simp [yZ] at this) _ (yc Z.1 (jM.1 Z).2 λ i=>by fin_cases i<;>simp [(jM.1 h).2,(jM.1 hU).2,(jM.1 hW).2,u1,u2,u3,w1,w2,w3,y0 X h]);exact ⟨t,λ i j=>by have:=congrFun e (i,j);simp at this;grind⟩
 have s:∀ X∈qK L,∀ x:Fin 3->KD,X (1,1)*(X (2,0)*(-(p*q)*x 1+q*x 2)+X (3,0)*(p*x 1+x 2))+x 0*(X (2,0)*(-(p*q)*X (1,2)+q*X (1,3))+X (3,0)*(p*X (1,2)+X (1,3)))=0:=λ X h x=>by
  obtain ⟨Y,a,rfl⟩:=qz hL hr x;obtain ⟨-,b,c,d⟩:=ws h;have e1:=vX hL hT (add_mem a h.1);have e2:=vX hL hT (sub_mem a h.1);have e0:=vX hL hT a;simp only [W7,map_add,map_sub,b,Pi.add_apply,Pi.sub_apply,yO,jm,c,d] at e1 e2 e0;simp [y0 X h] at e1 e2;grind
 have a1:=s U hU (Pi.single 1 1);have a2:=s W hW (Pi.single 2 1);have b1:=s U hU (Pi.single 0 1);have b2:=s W hW (Pi.single 0 1);have b3:=s _ (add_mem hU hW) (Pi.single 0 1);simp [u2,u3,w2,w3] at a1 a2 b1 b2 b3;have U11:U (1,1)=0:=by grind
 have U13:U (1,3)=p*U (1,2):=by grind
 have W13:W (1,3)=-p*W (1,2):=by grind
 have U12:U (1,2)=q*W (1,2):=by grind
 have r1:∀ X∈qK L,X (1,1)=0/\X (1,2)=W (1,2)*(q*X (2,0)+X (3,0))/\X (1,3)=W (1,2)*p*(q*X (2,0)-X (3,0)):=λ X h=>by have ⟨t,e⟩:=dec X h;refine ⟨?_,?_,?_⟩<;>rw [e]<;>simp [yZ,U11,a2,U12,U13,W13]<;>ring
 refine ⟨U,W,hU,hW,u1,u2,u3,w1,w2,w3,?_⟩;by_cases κ:W (1,2)=0
 . left;intro X h j;have ⟨a,b,c⟩:=r1 X h;fin_cases j<;>simp [y0 X h,a,b,c,κ]
 right;refine ⟨_,κ,λ X h=>⟨?_,(r1 X h).2⟩⟩;have d0:∀ X∈qK L,X (1,1)=0->X (2,1)*(-(p*q)*X (1,2)+q*X (1,3))+X (3,1)*(p*X (1,2)+X (1,3))=0:=λ X h e=>by have a:=(ks hL hr (add_mem h hT.1)).1;have b:=(ks hL hr h).1;simp [yZ,e] at a b;grind
 have c1:=d0 U hU U11;have c2:=d0 W hW a2;have c3:=d0 _ (add_mem hU hW) (by simp [U11,a2]);have c4:=(ks hL hr (add_mem hU hW)).2.2.1;simp [U11,a2,u1,u2,u3,w1,w2,w3,U12,U13,W13] at c1 c2 c3 c4;have:U (3,1)=0/\W (2,1)=0/\W (3,1)=0/\U (2,1)=0:=by clear d0 dec s r1 mk hrel hlift;grind
 have ⟨t,e⟩:=dec X h;intro i;rw [e];fin_cases i<;>simp [yZ,(jM.1 hU).2,(jM.1 hW).2,U11,a2,this]
theorem We {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {f:Fin 3->KD} {g0:KD} (hg:g0≠0) (hrel:∀ Y∈L,∑ k,f k*zw Y k=g0*zB Y 0) (hlift:∀ x y,∑ k,f k*x k=g0*y 0->∃ Y∈L,zw Y=x/\zB Y=y):False:=by
 have ⟨U,W,hU,hW,u1,u2,u3,w1,w2,w3,c⟩:=Kc H hp hq hpq hT hg hrel hlift;obtain ⟨hL,h6,hr,-,-⟩:=id H;obtain ⟨l,hl,-⟩:=(qu hL hr).2;obtain ⟨j,hj⟩:∃ j,l (Pi.single j 1)≠0:=by
  by_contra h;push Not at h;have:l (λ _=>(1:KD))=1:=by simpa using hl 1 0 (zero_mem _)
  rw [←Finset.univ_sum_single (λ _:Fin 4=>(1:KD)),map_sum] at this;simp [h] at this
 rcases c with c|⟨κ,k,hK⟩
 . exact Wa H hp hq hT hl hj c
 have ⟨uc,a,b⟩:=hK U hU;have ⟨wc,c,d⟩:=hK W hW;by_cases e:j=2\/j=3
 . obtain ⟨M,hM⟩:=Qi hL hr hl j;have hc:zo (z7 0 j M)≠0:=by have:=hM 0 (zero_mem _);rw [add_zero] at this;rw [this];exact mul_ne_zero (by norm_num) (pow_ne_zero _ hj)
   have hd:∀ X∈qK L,qm (z7 0 j X) (z7 0 j M)=0:=λ X h=>(W8 (z7 0 j M) (z7 0 j X) _ λ s=>by rw [←map_smul,←map_add];exact hM _ (smul_mem _ s h)).2.1
   have d1:=hd U hU;have d2:=hd _ (add_mem hU hT.1);have d3:=hd W hW;apply hc;clear hd hK hM hrel hlift hl;rcases e with rfl|rfl<;>simp [qm,zs,zK,z6,Fin.sum_univ_three,zt,z8,yZ,u1,u2,u3,w1,w2,w3,uc,wc,a,b,c,d] at d1 d2 d3⊢<;>grind
 by_cases e:j=1
 . subst e;obtain ⟨B,hB,hN,-⟩:=Qj hL h6 hr hl hj;have hN:∀ X∈(qK L).map (z7 0 1),zo (B+X)=zo B:=λ X ⟨Y,h,e⟩=>e▸hN Y h;have r1:=Wd hB hN (mem_map_of_mem hT.1) (mem_map_of_mem hU) (mem_map_of_mem hW) 1;have r2:=Wd hB hN (mem_map_of_mem hT.1) (mem_map_of_mem hU) (mem_map_of_mem hW) 2;simp only [vY,zt] at r1 r2;simp [z8,yZ,u2,u3,w2,w3,a,b,c,d] at r1 r2;clear hN hK hl hrel hlift;have R2:U (3,3)=-p*U (3,2):=by grind
   have W3:W (2,3)=p*W (2,2):=by grind
   have C1:q*U (2,2)=U (3,2)-q*(W (3,2)-q*W (2,2)):=by grind
   have C2:q*U (2,3)=p*U (3,2)-q*(W (3,3)+p*q*W (2,2)):=by have:κ*p^2*(q*U (2,3)-p*U (3,2)+q*(W (3,3)+p*q*W (2,2)))=0:=(by linear_combination -r2.2-κ*p^2*R2-κ*p^2*q^2*W3);simp [k,hp] at this;grind
   have P:=λ t u w:KD=>(qb hL (jM.1 (add_mem (add_mem (smul_mem _ t hT.1) (smul_mem _ u hU)) (smul_mem _ w hW))).1).2.1;have p1:=P (-U (3,2)) q 0;have p2:=P (-W (2,2)) 0 1;have p3:=P (-U (3,2)-q*W (2,2)) q q;have p4:=P (q-U (3,2)) q 0;simp [yl,Fintype.sum_prod_type,Fin.sum_univ_four,yZ,(jM.1 hU).2,(jM.1 hW).2,uc,wc,u1,u2,u3,w1,w2,w3,a,b,c,d,R2,W3,C1,C2] at p1 p2 p3 p4;have:q^3*κ*(1+p-(W (3,3)+p*q*W (2,2))-p*(W (3,2)-q*W (2,2)))=0:=by linear_combination p1/2
   have:κ*(1-p+(W (3,3)+p*q*W (2,2))-p*(W (3,2)-q*W (2,2)))=0:=by linear_combination p2/2
   have:q^2*(2*κ*(q+1)+2*κ*p*(q-1)-2*(W (3,2)-q*W (2,2))*(W (3,3)+p*q*W (2,2)))=0:=by linear_combination p3/2
   have:q^3*(κ*(1+3*p-(W (3,3)+p*q*W (2,2))-p*(W (3,2)-q*W (2,2)))+(1-p+p*(W (3,2)-q*W (2,2))-(W (3,3)+p*q*W (2,2))))=0:=by linear_combination p4/2
   clear P p1 p2 p3 p4 r1 r2 C1 C2;grind
 have:j=0:=by revert e;revert e;fin_cases j<;>decide
 subst this;exact Wb H hp hq hpq hT hl hj λ X h=>(hK X h).1
theorem Qk {L} (H:kr L) {p q:KD} (_:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {g:Fin 3->KD} (hG:g 1≠0\/g 2≠0) (hl:∀ a b c:KD,g 0*a+g 1*b+g 2*c=0->∃ H∈qK L,H (1,0)=a/\H (2,0)=b/\H (3,0)=c) {θ:KD} (hK:∀ H∈qK L,H (1,1)=θ*H (1,0)/\H (2,1)=-θ*H (2,0)/\H (3,1)=-θ*H (3,0)) (h0:∀ H∈qK L,H (1,2)=0/\H (1,3)=0):False:=by
 obtain ⟨hL,-,hr,-,-⟩:=id H;obtain ⟨e,he,e0⟩:∃ H∈qK L,H (1,0)=1:=by rcases hG with h|h;exacts [let ⟨H,a,b,_⟩:=hl 1 (-g 0/g 1) 0 (by grind);⟨H,a,b⟩,let ⟨H,a,b,_⟩:=hl 1 0 (-g 0/g 2) (by grind);⟨H,a,b⟩]
 have per:∀ H∈qK L,H (2,2)*H (3,3)+H (2,3)*H (3,2)=0:=λ H h=>by
  have:=yh (qK L) (zf (1,0)) (yi (zf (2,2)) (zf (3,3)) (zf (2,3)) (zf (3,2))) he (by simp [zf,e0]) (λ H h=>by have:=(ks hL hr h).2.1;have ⟨a,b⟩:=h0 H h;simp only [zU,zf,proj_apply];rw [a,b] at this;grind) H h;simpa [zU,zf] using this
 have PP:∀ H∈qK L,(1+θ)*H (1,0)+(1-θ)*(H (2,0)+H (3,0))+(H (2,2)+H (2,3)+H (3,2)+H (3,3))=0/\-2*θ*H (2,0)*H (3,0)+(1-θ)*(H (2,0)*(H (3,2)+H (3,3))+H (3,0)*(H (2,2)+H (2,3)))+(1+θ)*H (1,0)*(H (2,2)+H (2,3)+H (3,2)+H (3,3))+(H (2,2)*H (3,3)+H (2,3)*H (3,2))=0:=λ H h=>by
  have:=qb hL h.1;have ⟨a,b,c⟩:=hK H h;have ⟨d,e⟩:=h0 H h;simp [qY,yl,Fintype.sum_prod_type,Fin.sum_univ_four,(jM.1 h).2,a,b,c,d,e] at this;exact ⟨by grind,by grind⟩
 have tc:∀ H∈qK L,(1-θ)*(H (3,0)-H (2,0))=0:=λ H h=>by
  have a:=(PP H h).2;have b:=(PP _ (add_mem h hT.1)).2;have c:=per H h;have d:=per _ (add_mem h hT.1);simp [yZ] at b d;clear PP per hK h0 hl;grind
 by_cases t:θ=1
 . subst t;rcases hG with h|h
   . have ⟨H,a,b,c,d⟩:=hl (g 1) (-g 0) 0 (by ring);have u:=PP H a;have v:=per H a;rw [b,c,d] at u;clear PP per hK h0 hl tc;grind
   . have ⟨H,a,b,c,d⟩:=hl (g 2) 0 (-g 0) (by ring);have u:=PP H a;have v:=per H a;rw [b,c,d] at u;clear PP per hK h0 hl tc;grind
 have y:∀ H∈qK L,H (3,0)=H (2,0):=λ H h=>by have:=tc H h;grind
 obtain ⟨H,a,-,b,c⟩:=hl (g 1) (-g 0) 0 (by ring);have u:=y H a;rw [b,c] at u;obtain ⟨H',a',-,b',c'⟩:=hl 0 (g 2) (-g 1) (by ring);have v:=y H' a';rw [b',c'] at v;have ⟨A,hA,a0,a1,a2⟩:=hl 1 0 0 (by grind);have ⟨B,hB,b0,b1,b2⟩:=hl 0 1 1 (by grind);have w:=PP A hA;have x:=PP B hB;have z:=per A hA;have z':=per B hB;rw [a0,a1,a2] at w;rw [b0,b1,b2] at x;clear PP per hK h0 hl tc y;grind
theorem Wf {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {g:Fin 3->KD} (hG:g 1≠0\/g 2≠0) (hl:∀ a b c:KD,g 0*a+g 1*b+g 2*c=0->∃ H∈qK L,H (1,0)=a/\H (2,0)=b/\H (3,0)=c) {θ:KD} (t:θ≠0) (hK:∀ H∈qK L,H (1,1)=θ*H (1,0)/\H (2,1)=-θ*H (2,0)/\H (3,1)=-θ*H (3,0)) (y:∀ H∈qK L,H (2,0)=0):False:=by
 obtain ⟨hL,-,hr,-,-⟩:=id H;have g0:g 0=0:=by obtain ⟨H,a,-,b,-⟩:=hl (g 1) (-g 0) 0 (by ring);have:=y H a;rw [b] at this;grind
 have g2:g 2=0:=by obtain ⟨H,a,-,b,-⟩:=hl 0 (g 2) (-g 1) (by ring);have:=y H a;rw [b] at this;exact this
 have ⟨A,hA,a0,a1,a2⟩:=hl 1 0 0 (by rw [g0];ring);have ⟨B,hB,b0,b1,b2⟩:=hl 0 0 1 (by rw [g2];ring);have D:∀ H∈qK L,H (1,0)*(H (2,2)*H (3,3)+H (2,3)*H (3,2))=0/\H (3,0)*(H (1,2)*H (2,3)+H (1,3)*H (2,2))=0:=λ H h=>by
  obtain ⟨u,v,-⟩:=ks hL hr h;have ⟨a,b,c⟩:=hK H h;have:=y H h;rw [a,b,c,this] at u;rw [this] at v;constructor<;>grind
 have per:∀ H∈qK L,H (2,2)*H (3,3)+H (2,3)*H (3,2)=0:=λ H h=>by
  have:=yh (qK L) (zf (1,0)) (yi (zf (2,2)) (zf (3,3)) (zf (2,3)) (zf (3,2))) hA (by simp [zf,a0]) (λ H h=>by simp only [zU,zf,proj_apply];exact (D H h).1) H h;simpa [zU,zf] using this
 have Φ:∀ H∈qK L,H (1,2)*H (2,3)+H (1,3)*H (2,2)=0:=λ H h=>by
  have:=yh (qK L) (zf (3,0)) (yi (zf (1,2)) (zf (2,3)) (zf (1,3)) (zf (2,2))) hB (by simp [zf,b2]) (λ H h=>by simp only [zU,zf,proj_apply];exact (D H h).2) H h;simpa [zU,zf] using this
 have r3:∀ H∈qK L,H (1,3)=-p*H (1,2):=λ H h=>by have a:=Φ H h;have b:=Φ _ (add_mem h hT.1);simp [yZ] at b;grind
 by_cases r2:∀ H∈qK L,H (1,2)=0
 . exact Qk H hp hq hpq hT hG hl hK λ H h=>⟨r2 H h,by rw [r3 H h,r2 H h];ring⟩
 have A23:∀ H∈qK L,H (2,3)=p*H (2,2):=by
  rcases zz (qK L) (zf (1,2)) (zf (2,3)-p•zf (2,2)) (λ H h=>by have:=Φ H h;rw [r3 H h] at this;simp only [zf,LinearMap.sub_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul];grind) with h|h
  . exact absurd (λ H g=>by simpa [zf] using h H g) r2
  . exact λ H g=>by have:=h H g;simp only [zf,LinearMap.sub_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul] at this;grind
 have A33:∀ H∈qK L,H (3,3)=-p*H (3,2):=by
  rcases zz (qK L) (zf (2,2)) (zf (3,3)+p•zf (3,2)) (λ H h=>by have:=per H h;rw [A23 H h] at this;simp only [zf,LinearMap.add_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul];grind) with h|h
  . have:=h _ hT.1;simp [zf,yZ] at this
  . exact λ H g=>by have:=h H g;simp only [zf,LinearMap.add_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul] at this;grind
 have P:=λ (X:ze) (x:X∈qK L) (t:KD)=>qb hL (jM.1 (add_mem (smul_mem _ t hT.1) x)).1;have pA:=P _ (sub_mem (smul_mem _ q hA) (smul_mem _ (A (3,2)) hT.1)) 0;have pB:=P _ (sub_mem (smul_mem _ q hB) (smul_mem _ (B (3,2)) hT.1)) 0;have pC:=P _ (sub_mem (smul_mem _ q hA) (smul_mem _ (A (3,2)) hT.1)) 1;have ⟨u1,u2,u3⟩:=hK A hA;have ⟨v1,v2,v3⟩:=hK B hB;simp [qY,yl,Fintype.sum_prod_type,Fin.sum_univ_four,yZ,(jM.1 hA).2,(jM.1 hB).2,a0,a1,a2,b0,b1,b2,u1,u2,u3,v1,v2,v3,r3 A hA,r3 B hB,A23 A hA,A23 B hB,A33 A hA,A33 B hB] at pA pB pC;have A2:q*(1+θ)*(1+p)*(q*A (2,2)-A (3,2))=0:=by linear_combination pA.2.1/2
 have B2:q*(1-θ)*(q*(1-p)*B (1,2)+(1+p)*(q*B (2,2)-B (3,2)))=0:=by linear_combination pB.2.1/2
 have T2:q*(1+θ)*(1+p)*(q*A (2,2)-A (3,2))+q*(1+θ)*(1+p+q-p*q)-2*p*q^2*A (1,2)=0:=by linear_combination pC.2.1/2
 have r:A (1,2)=0:=by have:2*p*q^2*A (1,2)=0:=(by linear_combination -(T2-A2)+q*(1+θ)*hpq);simpa [hp,hq] using this
 exact hq (by linear_combination ((pow_eq_zero_iff two_ne_zero).1 (by linear_combination q*(1-θ)*pB.1-B2:(q*(1-θ))^2=0)+(pow_eq_zero_iff two_ne_zero).1 (by linear_combination q*(1+θ)*pA.1-A2-q^2*(1+θ)*(1-p)*r:(q*(1+θ))^2=0))/2)
theorem Wg {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {g:Fin 3->KD} (hG:g 1≠0\/g 2≠0) (hl:∀ a b c:KD,g 0*a+g 1*b+g 2*c=0->∃ H∈qK L,H (1,0)=a/\H (2,0)=b/\H (3,0)=c) {θ:KD} (t:θ≠0) (hK:∀ H∈qK L,H (1,1)=θ*H (1,0)/\H (2,1)=-θ*H (2,0)/\H (3,1)=-θ*H (3,0)) (y:∀ H∈qK L,H (3,0)=0):False:=by
 obtain ⟨hL,-,hr,-,-⟩:=id H;have g0:g 0=0:=by obtain ⟨H,a,-,-,b⟩:=hl (g 2) 0 (-g 0) (by ring);have:=y H a;rw [b] at this;grind
 have g1:g 1=0:=by obtain ⟨H,a,-,-,b⟩:=hl 0 (g 2) (-g 1) (by ring);have:=y H a;rw [b] at this;grind
 have ⟨A,hA,a0,a1,a2⟩:=hl 1 0 0 (by rw [g0];ring);have ⟨B,hB,b0,b1,b2⟩:=hl 0 1 0 (by rw [g1];ring);have D:∀ H∈qK L,H (1,0)*(H (2,2)*H (3,3)+H (2,3)*H (3,2))=0/\H (2,0)*(H (1,2)*H (3,3)+H (1,3)*H (3,2))=0:=λ H h=>by
  obtain ⟨u,v,-⟩:=ks hL hr h;have ⟨a,b,c⟩:=hK H h;have:=y H h;rw [a,b,c,this] at u;rw [this] at v;constructor<;>grind
 have per:∀ H∈qK L,H (2,2)*H (3,3)+H (2,3)*H (3,2)=0:=λ H h=>by
  have:=yh (qK L) (zf (1,0)) (yi (zf (2,2)) (zf (3,3)) (zf (2,3)) (zf (3,2))) hA (by simp [zf,a0]) (λ H h=>by simp only [zU,zf,proj_apply];exact (D H h).1) H h;simpa [zU,zf] using this
 have Ψ:∀ H∈qK L,H (1,2)*H (3,3)+H (1,3)*H (3,2)=0:=λ H h=>by
  have:=yh (qK L) (zf (2,0)) (yi (zf (1,2)) (zf (3,3)) (zf (1,3)) (zf (3,2))) hB (by simp [zf,b1]) (λ H h=>by simp only [zU,zf,proj_apply];exact (D H h).2) H h;simpa [zU,zf] using this
 have r3:∀ H∈qK L,H (1,3)=p*H (1,2):=λ H h=>by have a:=Ψ H h;have b:=Ψ _ (add_mem h hT.1);simp [yZ] at b;clear Ψ per D hK hl y;grind
 by_cases r2:∀ H∈qK L,H (1,2)=0
 . exact Qk H hp hq hpq hT hG hl hK λ H h=>⟨r2 H h,by rw [r3 H h,r2 H h];ring⟩
 have A33:∀ H∈qK L,H (3,3)=-p*H (3,2):=by
  rcases zz (qK L) (zf (1,2)) (zf (3,3)+p•zf (3,2)) (λ H h=>by have:=Ψ H h;rw [r3 H h] at this;simp only [zf,LinearMap.add_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul];grind) with h|h
  . exact absurd (λ H g=>by simpa [zf] using h H g) r2
  . exact λ H g=>by have:=h H g;simp only [zf,LinearMap.add_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul] at this;grind
 have A23:∀ H∈qK L,H (2,3)=p*H (2,2):=by
  rcases zz (qK L) (zf (3,2)) (zf (2,3)-p•zf (2,2)) (λ H h=>by have:=per H h;rw [A33 H h] at this;simp only [zf,LinearMap.sub_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul];grind) with h|h
  . have:=h _ hT.1;simp [zf,yZ] at this;exact (hq this).elim
  . exact λ H g=>by have:=h H g;simp only [zf,LinearMap.sub_apply,LinearMap.smul_apply,proj_apply,smul_eq_mul] at this;grind
 have P:=λ (X:ze) (x:X∈qK L) (t:KD)=>qb hL (jM.1 (add_mem (smul_mem _ t hT.1) x)).1;have pA:=P _ (sub_mem hA (smul_mem _ (A (2,2)) hT.1)) 0;have pB:=P _ (sub_mem hB (smul_mem _ (B (2,2)) hT.1)) 0;have pC:=P _ (sub_mem hA (smul_mem _ (A (2,2)) hT.1)) 1;have ⟨u1,u2,u3⟩:=hK A hA;have ⟨v1,v2,v3⟩:=hK B hB;simp [qY,yl,Fintype.sum_prod_type,Fin.sum_univ_four,yZ,(jM.1 hA).2,(jM.1 hB).2,a0,a1,a2,b0,b1,b2,u1,u2,u3,v1,v2,v3,r3 A hA,r3 B hB,A23 A hA,A23 B hB,A33 A hA,A33 B hB] at pA pB pC;clear P D per Ψ r3 A23 A33 hK hl y r2;grind
theorem Kd {L} (hL:zg L) {p q:KD} (hp:p≠0) (hq:q≠0) (hT:yZ p q∈zm L 0 0) {f g:Fin 3->KD} (hl:∀ x y,∑ k,f k*x k=∑ k,g k*y k->∃ Y∈L,zw Y=x/\zB Y=y) (hF:f 1≠0\/f 2≠0) (hG:g 1≠0\/g 2≠0):∃ θ:KD,∀ H∈qK L,H (1,1)=θ*H (1,0)/\H (2,1)=-θ*H (2,0)/\H (3,1)=-θ*H (3,0):=by
 have sol:∀ v:Fin 3->KD,(v 1≠0\/v 2≠0)->∀ c:KD,∃ y:Fin 3->KD,y 0=0/\∑ k,v k*y k=c:=λ v h c=>by rcases h with h|h;exacts [⟨Pi.single 1 (c/v 1),by simp,by rw [qQ];field_simp⟩,⟨Pi.single 2 (c/v 2),by simp,by rw [qQ];field_simp⟩]
 let N0:=L⊓ker (qj 0)⊓ker (qq 0);have m0:∀ Y,Y∈N0↔Y∈L/\zw Y 0=0/\zB Y 0=0:=λ Y=>by simp only [N0,mem_inf,mem_ker,zJ,zG,and_assoc]
 let Qb:=yi (qq 1) (-(p*q)•qj 1+q•qj 2) (qq 2) (p•qj 1+qj 2);have hQ:∀ Y,Qb Y Y=zB Y 1*(-(p*q)*zw Y 1+q*zw Y 2)+zB Y 2*(p*zw Y 1+zw Y 2):=λ Y=>by simp [Qb,zU,zJ,zG]
 obtain ⟨e,he,hq0⟩:∃ e∈N0,Qb e e≠0:=by
  by_contra c;push Not at c;obtain ⟨x0,-,a⟩:=sol ![0,f 1,f 2] (by simpa using hF) 1;obtain ⟨y0,-,b⟩:=sol ![0,g 1,g 2] (by simpa using hG) 1;have z:=qC (LinearMap.mk₂ KD (λ x y:Fin 3->KD=>y 1*(-(p*q)*x 1+q*x 2)+y 2*(p*x 1+x 2)) (by intros;simp only [Pi.add_apply];ring) (by intros;simp only [Pi.smul_apply,smul_eq_mul];ring) (by intros;simp only [Pi.add_apply];ring) (by intros;simp only [Pi.smul_apply,smul_eq_mul];ring)) (qf ![0,f 1,f 2]) (qf ![0,g 1,g 2]) (x0:=x0) (y0:=y0) a b λ x y h=>by
   have ⟨Y,h,u,v⟩:=hl ![0,x 1,x 2] ![0,y 1,y 2] (by have d:∀ v x:Fin 3-> KD,qf v x=∑ k,v k*x k:=λ _ _=>rfl;rw [d,d] at h;simp only [Fin.sum_univ_three,Matrix.cons_val] at h ⊢;grind);have:=c Y ((m0 Y).2 ⟨h,by rw [u];rfl,by rw [v];rfl⟩);rw [hQ,u,v] at this;simpa using this
  have:=z (Pi.single 2 1) (Pi.single 2 1);simp at this
 have s0:∀ Y∈N0,yg 0 0 Y=0:=kf N0 (yg 0 0) Qb he hq0 λ Y h=>by have ⟨u,v,w⟩:=(m0 Y).1 h;have:=vX hL hT u;simp only [W7] at this;rw [v,w] at this;rw [qx,hQ];grind
 have ⟨ya,ya0,a⟩:=sol g hG (f 0);have ⟨xb,xb0,b⟩:=sol f hF (g 0);have ⟨Ya,ha,xa,yy⟩:=hl (Pi.single 0 1) ya (by rw [qQ,mul_one,a]);have ⟨Yb,hb,xx,yb⟩:=hl xb (Pi.single 0 1) (by rw [qQ,mul_one,b]);have hs:∀ Y∈L,zv Y 0 0=zv Ya 0 0*zw Y 0+zv Yb 0 0*zB Y 0:=λ Y h=>by
  have:=s0 _ ((m0 _).2 ⟨sub_mem (sub_mem h (smul_mem _ (zw Y 0) ha)) (smul_mem _ (zB Y 0) hb),by simp [xa,xx,xb0],by simp [yy,yb,ya0]⟩);simp only [map_sub,map_smul,qx,smul_eq_mul] at this;grind
 set θ:=zv Yb 0 0;let N1:=L⊓ker (qj 0);have m1:∀ Y,Y∈N1↔Y∈L/\zw Y 0=0:=λ Y=>by simp only [N1,mem_inf,mem_ker,zJ]
 let Q2:=yi (θ•qq 1+yg 1 0) (-(p*q)•qj 1+q•qj 2) (θ•qq 2+yg 2 0) (p•qj 1+qj 2);have h2:∀ U V,Q2 U V=(θ*zB U 1+zv U 1 0)*(-(p*q)*zw V 1+q*zw V 2)+(θ*zB U 2+zv U 2 0)*(p*zw V 1+zw V 2):=λ U V=>by simp [Q2,zU,zJ,zG,qx]
 have ⟨y1,y10,c⟩:=sol g hG (-g 0);have ⟨E,hE,x1,yE⟩:=hl 0 (Pi.single 0 1+y1) (by simp [mul_add,Finset.sum_add_distrib,qQ,c]);have q0:∀ Y∈N1,Q2 Y Y=0:=yh N1 (qq 0) Q2 ((m1 _).2 ⟨hE,by rw [x1];rfl⟩) (by rw [zG,yE];simp [y10]) λ Y h=>by
  have ⟨u,v⟩:=(m1 Y).1 h;have:=vX hL hT u;simp only [W7] at this;rw [hs Y u,v] at this;rw [zG,h2];grind
 have pol:∀ H∈qK L,∀ Y∈N1,(θ*zB H 1+zv H 1 0)*(-(p*q)*zw Y 1+q*zw Y 2)+(θ*zB H 2+zv H 2 0)*(p*zw Y 1+zw Y 2)=0:=λ H h Y y=>by
  have x:=(ws h).2.1;have ⟨u,v⟩:=(m1 Y).1 y;have a:=q0 (Y+H) ((m1 _).2 ⟨add_mem u h.1,by rw [map_add,x,add_zero];exact v⟩);have b:=q0 Y y;rw [h2] at a b;simp only [map_add,Pi.add_apply,yO,x,Pi.zero_apply,add_zero] at a;grind
 obtain ⟨u1,-,c1⟩:=sol g hG (f 1);obtain ⟨u2,-,c2⟩:=sol g hG (f 2);obtain ⟨Y1,h1,e1,-⟩:=hl (Pi.single 1 1) u1 (by rw [qQ,mul_one,c1]);obtain ⟨Y2,h2',e2,-⟩:=hl (Pi.single 2 1) u2 (by rw [qQ,mul_one,c2]);refine ⟨θ,λ H h=>?_⟩;have a:=pol H h Y1 ((m1 _).2 ⟨h1,by rw [e1];rfl⟩);have b:=pol H h Y2 ((m1 _).2 ⟨h2',by rw [e2];rfl⟩);rw [e1] at a;rw [e2] at b;have d:=hs H h.1;obtain ⟨-,x,yy,bb⟩:=ws h;simp [x,yy,bb] at a b d;clear pol q0 hs sol h2 hQ s0 hl;grind
theorem KC {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0) {f g:Fin 3->KD} (hlift:∀ x y,∑ k,f k*x k=∑ k,g k*y k->∃ Y∈L,zw Y=x/\zB Y=y) (hF:f 1≠0\/f 2≠0) (hG:g 1≠0\/g 2≠0) {l:(Fin 4->KD)→ₗ[KD]KD} (hl:∀ a,∀ T∈L,l (λ j=>a+T (0,j))=a) (hj:l (Pi.single 0 1)≠0):False:=by
 obtain ⟨hL,-,hr,-,-⟩:=id H;have ⟨θ,hK⟩:=Kd hL hp hq hT hlift hF hG;by_cases t:θ=0
 . exact Wb H hp hq hpq hT hl hj λ X h i=>by have ⟨a,b,c⟩:=hK X h;fin_cases i<;>simp [(jM.1 h).2,a,b,c,t]
 have l3:∀ a b c:KD,g 0*a+g 1*b+g 2*c=0->∃ X∈qK L,X (1,0)=a/\X (2,0)=b/\X (3,0)=c:=λ a b c h=>by
  have ⟨X,u,v,w⟩:=hlift 0 ![a,b,c] (by simp [Fin.sum_univ_three];grind);have k:=jM.2 ⟨u,jl hL u v⟩;rw [(ws k).2.2.1] at w;exact ⟨X,k,congrFun w 0,congrFun w 1,congrFun w 2⟩
 have pr:∀ r:Fin 4,(∀ S∈qK L,S (1,r)*S (2,0)*S (3,0)=0)->(∀ S∈qK L,S (2,0)=0)\/(∀ S∈qK L,S (3,0)=0)\/∀ S∈qK L,S (1,r)=0:=λ r h=>by
  obtain ⟨i,-,e⟩:=yS (qK L) (λ _=>(0:KD)) ![zf (2,0),zf (3,0),zf (1,r)] λ S s=>by rw [Fin.prod_univ_three];simp only [Matrix.cons_val,zf,proj_apply,zero_add];grind
  fin_cases i;exacts [Or.inl λ S s=>by simpa [zf] using e S s,Or.inr (Or.inl λ S s=>by simpa [zf] using e S s),Or.inr (Or.inr λ S s=>by simpa [zf] using e S s)]
 have tw:∀ S∈qK L,S (1,3)*S (2,0)*S (3,0)=0/\S (1,2)*S (2,0)*S (3,0)=0:=λ S s=>by
  obtain ⟨-,-,u,v⟩:=ks hL hr s;have ⟨a,b,c⟩:=hK S s;rw [a,b,c] at u v;constructor<;>grind
 rcases pr 3 λ S s=>(tw S s).1 with h|h|h3
 . exact Wf H hp hq hpq hT hG l3 t hK h
 . exact Wg H hp hq hpq hT hG l3 t hK h
 rcases pr 2 λ S s=>(tw S s).2 with h|h|h2
 . exact Wf H hp hq hpq hT hG l3 t hK h
 . exact Wg H hp hq hpq hT hG l3 t hK h
 . exact Qk H hp hq hpq hT hG l3 hK λ H h=>⟨h2 H h,h3 H h⟩
theorem Ke {L} (H:kr L) {p q:KD} (hp:p≠0) (hq:q≠0) (hpq:1+p+q-p*q=0) (hT:yZ p q∈zm L 0 0):False:=by
 have ⟨hL,h6,hr,hc,hd⟩:=id H;obtain ⟨l,hl,-⟩:=(qu hL hr).2;obtain ⟨m,hm,-⟩:=(j3 hL hc).2;have fr:∀ f g:Fin 3->KD,f≠0->g≠0->(∀ Y∈L,∑ k,f k*zw Y k=∑ k,g k*zB Y k)->(∀ x y,∑ k,f k*x k=∑ k,g k*y k->∃ Y∈L,zw Y=x/\zB Y=y)->(f 1=0/\f 2=0)\/(g 1=0/\g 2=0)->False:=λ f g hf hg hrel hlift h=>by
  rcases h with h|h
  . have s:∀ y:Fin 3->KD,∑ k,f k*y k=f 0*y 0:=λ y=>by simp [Fin.sum_univ_three,h.1,h.2]
    refine We (W0 H) hq hp (by grind) ?_ (f:=g) (g0:=f 0) (λ e=>hf (funext λ k=>by fin_cases k;exacts [e,h.1,h.2])) ?_ ?_
    . rw [ja];refine ⟨_,hT,funext λ ⟨i,j⟩=>?_⟩;fin_cases i<;>fin_cases j<;>simp [yZ,zQ];ring
    . rintro _ ⟨Y,h,rfl⟩;have:=hrel Y h;rw [s] at this;exact this.symm
    . intro x y e;have ⟨Y,h,a,b⟩:=hlift y x (by rw [s];exact e.symm);exact ⟨zM Y,⟨Y,h,rfl⟩,b,a⟩
  . have s:∀ y:Fin 3->KD,∑ k,g k*y k=g 0*y 0:=λ y=>by simp [Fin.sum_univ_three,h.1,h.2]
    exact We H hp hq hpq hT (λ h0=>hg (funext λ k=>by fin_cases k;exacts [h0,h.1,h.2])) (λ Y h=>(hrel Y h).trans (s _)) λ x y e=>hlift x y (e.trans (s y).symm)
 by_cases h:∀ k:Fin 3,l (Pi.single k.succ 1)=0
 . have j0:l (Pi.single 0 1)≠0:=λ h0=>by
    have:l (λ _=>(1:KD))=1:=by simpa using hl 1 0 (zero_mem _)
    rw [←Finset.univ_sum_single (λ _:Fin 4=>(1:KD)),map_sum,Fin.sum_univ_succ] at this;simp [h0,h] at this
   have ⟨f,g,hf,hg,hrel,hlift⟩:=W5 H;by_cases h:(f 1=0/\f 2=0)\/(g 1=0/\g 2=0)
   . exact fr f g hf hg hrel hlift h
   . exact KC H hp hq hpq hT hlift (by tauto) (by tauto) hl j0
 push Not at h;have ⟨k0,k⟩:=h;have lm:∀ Y∈L,∑ k,l (Pi.single k.succ 1)*zw Y k=∑ k,m (Pi.single k.succ 1)*zB Y k:=λ Y h=>(kK hl h).trans (vr hm h).symm;have ln:(λ k:Fin 3=>l (Pi.single k.succ 1))≠0:=λ h=>k (congrFun h k0);have mn:(λ k:Fin 3=>m (Pi.single k.succ 1))≠0:=λ h=>k (by have ⟨Y,a,b⟩:=qz hL hr (Pi.single k0 1);have:=lm Y a;rw [b,qQ] at this;simpa [congrFun h] using this);by_cases h:(l (Pi.single (1:Fin 3).succ 1)=0/\l (Pi.single (2:Fin 3).succ 1)=0)\/(m (Pi.single (1:Fin 3).succ 1)=0/\m (Pi.single (2:Fin 3).succ 1)=0)
 . exact fr _ _ ln mn lm (vs hL h6 hd _ _ lm ln) h
 push Not at h;refine yn hL h6 hr hc hd hl hm hT (r0:=0) (c0:=0) (λ c=>?_) (λ r=>?_) (λ r a c b=>?_) ?_ ?_
 . fin_cases c<;>simp [qL,yZ]
 . fin_cases r<;>simp [qL,yZ]
 . fin_cases r<;>fin_cases c<;>simp [qL,yZ,hp,hq] at a b ⊢
 . by_contra c;push Not at c;exact h.1 c.1 c.2
 . by_contra c;push Not at c;exact h.2 c.1 c.2
theorem Wh {L} (H:kr L) (hF:yx) (hF5:∀ (L':Submodule KD ze),zg L'->Module.finrank KD L'=6->Module.finrank KD (L'.map (z9 0))=3->Module.finrank KD (L'.map (zD 0))=3->(∃ T∈zm L' 0 0,T≠0/\(∃ r:Fin 3,∀ i j:Fin 4,i≠r.succ->T (i,j)=0)/\(∃ c:Fin 3,∀ i:Fin 4,T (i,c.succ)=0))->False) {T:ze} (hT:T∈zm L 0 0) (h0:T≠0) {r0:Fin 3} (hw:∀ r,r≠r0->∀ c,z7 0 0 T r c=0):False:=by
 obtain ⟨-,t0,t0'⟩:=qJ hT;by_cases h:∃ c,z7 0 0 T r0 c=0
 . have ⟨c,e⟩:=h;refine hF5 L H.1 H.2.1 H.2.2.1 H.2.2.2.1 ⟨T,hT,h0,⟨r0,λ i j g=>?_⟩,⟨c,λ i=>?_⟩⟩
   . rcases Fin.eq_zero_or_eq_succ i with rfl|⟨a,rfl⟩;exact t0 j;rcases Fin.eq_zero_or_eq_succ j with rfl|⟨b,rfl⟩;exact t0' _;have:=hw a (λ h=>g (by rw [h])) b;rwa [qL] at this
   . refine Fin.cases (t0 _) (λ a=>?_) i;by_cases g:a=r0
     . subst g;rwa [qL] at e
     . have:=hw a g c;rwa [qL] at this
 push Not at h;have ⟨L',T',H',hT',hD⟩:=W4 H (Equiv.swap 0 r0) 1 hT;refine W6 H' hF hT' (λ a g b=>?_) λ b=>?_
 . rw [hD];exact hw _ (λ h=>g ((Equiv.swap 0 r0).injective (h.trans (Equiv.swap_apply_left 0 r0).symm))) _
 . rw [hD,Equiv.swap_apply_left];exact h _
theorem wt {L:Submodule KD ze} (hL:zg L) (h6:Module.finrank KD L=6) (hr:Module.finrank KD (L.map (z9 0))=3) (hc:Module.finrank KD (L.map (zD 0))=3) (hd1:Module.finrank KD (zm L 0 0)=1) (hF3:yx) (hF5c:∀ (L':Submodule KD ze),zg L'->Module.finrank KD L'=6->Module.finrank KD (L'.map (z9 0))=3->Module.finrank KD (L'.map (zD 0))=3->(∃ T∈zm L' 0 0,T≠0/\(∃ r:Fin 3,∀ i j:Fin 4,i≠r.succ->T (i,j)=0)/\(∃ c:Fin 3,∀ i:Fin 4,T (i,c.succ)=0))->False):False:=by
 have H:kr L:=⟨hL,h6,hr,hc,hd1⟩;have ⟨T,hT,h0⟩:=exists_mem_ne_zero_of_ne_bot (p:=zm L 0 0) λ h=>by rw [h,finrank_bot] at hd1;exact zero_ne_one hd1
 have D0:z7 0 0 T≠0:=λ h=>h0 (funext λ ⟨i,j⟩=>by obtain ⟨-,r,c⟩:=qJ hT;refine Fin.cases (r j) (λ a=>Fin.cases (c _) (λ b=>?_) j) i;have:=congrFun (congrFun h a) b;rwa [qL] at this);rcases qd _ D0 (yv hL h6 hr hc hd1 T hT) with ⟨r0,h⟩|⟨c0,h⟩|⟨r0,c0,h0r,h0c,hnz,-,-⟩
 . exact Wh H hF3 hF5c hT h0 h
 . refine Wh (W0 H) hF3 hF5c (T:=zM T) (by rw [ja];exact ⟨T,hT,rfl⟩) (λ h=>h0 (by simpa using congrArg zM.symm h)) (r0:=c0) λ r g c=>?_;have:=h r g c;rw [qL] at this ⊢;exact this
 . have hC:=yv hL h6 hr hc hd1 T hT;have ⟨L',T',H',hT',hD⟩:=W4 H (Equiv.swap 0 r0) (Equiv.swap 0 c0) hT;generalize z7 0 0 T=D at *;set σ:=Equiv.swap 0 r0;set τ:=Equiv.swap 0 c0;have sn:∀ a:Fin 3,a≠0->σ a≠r0:=λ a h e=>h (σ.injective (e.trans (Equiv.swap_apply_left 0 r0).symm));have tn:∀ a:Fin 3,a≠0->τ a≠c0:=λ a h e=>h (τ.injective (e.trans (Equiv.swap_apply_left 0 c0).symm));have a0:=hnz _ (sn 1 (by simp)) _ (tn 1 (by simp));have hp:=j6 hC (a:=σ 1) (a':=σ 2) (b:=τ 1) (b':=τ 2) (λ h=>absurd (σ.injective h) (by simp)) (λ h=>absurd (τ.injective h) (by simp));have E:∀ x y:Fin 3,T' (x.succ,y.succ)=D (σ x) (τ y):=λ x y=>by have:=hD x y;rwa [qL] at this
   obtain ⟨-,t0,t0'⟩:=qJ hT';have t1:∀ j,T' (1,j)=0:=λ j=>Fin.cases (t0' 1) (λ y=>by rw [show (1:Fin 4)=(0:Fin 3).succ from rfl,E,Equiv.swap_apply_left];exact h0r _) j;have t1':∀ i,T' (i,1)=0:=λ i=>Fin.cases (t0 1) (λ x=>by rw [show (1:Fin 4)=(0:Fin 3).succ from rfl,E,Equiv.swap_apply_left];exact h0c _) i;have t22:=E 1 1;have t23:=E 1 2;have t32:=E 2 1;have t33:=E 2 2;simp only [show (1:Fin 3).succ=2 from rfl,show (2:Fin 3).succ=3 from rfl] at t22 t23 t32 t33;have eT:(D (σ 1) (τ 1))⁻¹•T'=yZ (D (σ 1) (τ 2)/D (σ 1) (τ 1)) (D (σ 2) (τ 1)/D (σ 1) (τ 1)):=by
    funext ⟨i,j⟩;fin_cases i<;>fin_cases j<;>simp [yZ,t0,t0',t1,t1',t22,t23,t32,t33,a0];(all_goals field_simp);grind
   have h':=(zm L' 0 0).smul_mem (D (σ 1) (τ 1))⁻¹ hT';rw [eT] at h';have hP:=(qb H'.1 h'.1.1).1;simp [qY,Fintype.sum_prod_type,Fin.sum_univ_four,yZ] at hP;exact Ke H' (div_ne_zero (hnz _ (sn 1 (by simp)) _ (tn 2 (by simp))) a0) (div_ne_zero (hnz _ (sn 2 (by simp)) _ (tn 1 (by simp))) a0) (by grind) h'
end
section
open Module
private theorem xC (S:Submodule KD ze) (p q:Equiv.Perm (Fin 4)) (j:Fin 4) :
 finrank KD ((S.map (zq p q:ze→ₗ[KD]ze)).map (zD j))=finrank KD (S.map (zD (q j))):=by
 have h:(zD j).comp (zq p q:ze→ₗ[KD]ze)=(LinearEquiv.funCongrLeft KD KD p:(Fin 4->KD)→ₗ[KD](Fin 4->KD)).comp (zD (q j)):=by ext X i;rfl
 rw [←Submodule.map_comp,h,Submodule.map_comp];exact LinearEquiv.finrank_map_eq _ _
theorem Kf (L:Submodule KD (Fin 4×Fin 4->KD))
 (hE:∀ t∈L,MvPolynomial.eval (λ p=>1+t p) (PEqualNP.Gct.permPoly KD 4)=(Nat.factorial 4:KD)):finrank KD L<=5:=by
 by_contra hgt;push Not at hgt
 obtain ⟨L6,hle,h6⟩:=jV L (n:=6) hgt
 have hL6:zg L6:=λ t ht=>jN hE t (hle ht)
 obtain ⟨⟨i0,hi0⟩,⟨j0,hj0⟩⟩:=yL L6 hL6 h6
 let p:Equiv.Perm (Fin 4):=Equiv.swap 0 i0;let q:Equiv.Perm (Fin 4):=Equiv.swap 0 j0
 let L':Submodule KD ze:=L6.map (zq p q:ze→ₗ[KD]ze)
 have hL':zg L':=zH hL6 p q
 have h6':finrank KD L'=6:=(zF L6 p q).trans h6
 have hr:finrank KD (L'.map (z9 0))=3:=by change finrank KD ((L6.map (zq p q:ze→ₗ[KD]ze)).map (z9 0))=3;rw [yN];simp only [p];exact hi0
 have hc:finrank KD (L'.map (zD 0))=3:=by change finrank KD ((L6.map (zq p q:ze→ₗ[KD]ze)).map (zD 0))=3;rw [xC];simp only [q];exact hj0
 have hF3:yx:=Q9 (λ _ hL h6 hA=>wX hL h6 hA) (λ _ hL h6 hA hr0 hne=>kT hL h6 hA hr0 hne)
 have hF5c:∀ (L0:Submodule KD ze),zg L0->finrank KD L0=6->finrank KD (L0.map (z9 0))=3->finrank KD (L0.map (zD 0))=3->(∃ T∈zm L0 0 0,T≠0/\(∃ r:Fin 3,∀ i j:Fin 4,i≠r.succ->T (i,j)=0)/\(∃ c:Fin 3,∀ i:Fin 4,T (i,c.succ)=0))->False:=λ _ hL h6 hr0 hc0 hT=>yB hL h6 hr0 hc0 hT
 have hdle:finrank KD (zm L' 0 0)<=3:=(Submodule.finrank_mono (inf_le_left:zm L' 0 0<=zh L' 0)).trans (y5 h6' hr).le
 match hd:finrank KD (zm L' 0 0) with
 | 0=>exact wr hL' h6' hr hc hd
 | 1=>exact wt hL' h6' hr hc hd hF3 hF5c
 | 2=>exact wa hL' h6' hr hc hd hF3
 | 3=>exact we hL' h6' hr hc hd hF3
 | _+4=>omega
end
end PEqualNP.Outside.L_gct_091
theorem PEqualNP.Outside.L_gct_091 :
 ∀ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ),
  (∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = (Nat.factorial 4 : ℂ)) →
  Module.finrank ℂ L ≤ 5 :=
 PEqualNP.Outside.L_gct_091.Kf
