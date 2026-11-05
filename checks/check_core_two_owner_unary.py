"""Standalone audit of the native lower model for the Gamma_2 unary-12 lemma."""
from itertools import product
# 0,1 are atoms; 2..5 are markers with support 0..3; 6 is omega.
def join(x,y):
 if x==y:return x
 if 6 in (x,y):return 6
 sx=(1<<x) if x<2 else x-2
 sy=(1<<y) if y<2 else y-2
 return 2+(sx|sy)
def choice(i,x,y):return i if i in (x,y) else join(x,y)
def native_join(x,y):return x if x==y else max(2,x,y)
def native_choice(i,x,y):return i if i in (x,y) else native_join(x,y)
def observer(mask,x):
 if x==6:return 3
 if x<2:return x if mask>>x&1 else 3
 return 2 if (x-2)&~mask==0 else 3
images=[tuple(observer(mask,x) for mask in range(4)) for x in range(7)]
assert len(set(images))==7
entries=0
for mask,x,y in product(range(4),range(7),range(7)):
 assert observer(mask,join(x,y))==native_join(observer(mask,x),observer(mask,y));entries+=1
 for i in range(2):
  assert observer(mask,choice(i,x,y))==native_choice(i,observer(mask,x),observer(mask,y));entries+=1
forms={}
for ca,cb in product(range(3),repeat=2):
 values=[]
 for x in range(7):
  z=x
  if ca:z=join(z,choice(1,0,x) if ca==1 else join(x,0))
  if cb:z=join(z,choice(0,1,x) if cb==1 else join(x,1))
  values.append(z)
 forms[tuple(values)]=(ca,cb)
assert len(forms)==9
for a in (0,1,join(0,1)):forms[(a,)*7]=('constant',a)
assert len(forms)==12
closure_entries=0
for a,b in product(forms,repeat=2):
 assert tuple(join(x,y) for x,y in zip(a,b)) in forms;closure_entries+=1
 for i in range(2):
  assert tuple(choice(i,x,y) for x,y in zip(a,b)) in forms;closure_entries+=1
# Check the unconditional ordered-absorber identity in every native
# subalgebra with its actual global f-absorber, as used by the fold-lifting
# proof. No quasiidentity is transferred through homomorphic images.
ordered_subalgebras=ordered_entries=0
native_ops=[native_join]+[lambda x,y,i=i:native_choice(i,x,y) for i in range(2)]
for mask in range(1,16):
 subset=[x for x in range(4) if mask>>x&1]
 if any(h(x,y) not in subset for h in native_ops for x,y in product(subset,repeat=2)):continue
 absorbers=[a for a in subset if all(native_choice(0,a,x)==a for x in subset)]
 assert len(absorbers)==1
 a=absorbers[0];ordered_subalgebras+=1
 for x,y in product(subset,repeat=2):
  xy=native_join(x,y)
  assert native_choice(0,x,native_choice(1,a,xy))==native_choice(1,a,native_choice(0,x,xy))
  ordered_entries+=1
assert (ordered_subalgebras,ordered_entries)==(13,67)
print('PASS seven-state model; 4 native observers;',entries,'observer entries;',len(forms),'unary forms;',closure_entries,'unary products;',ordered_subalgebras,'pointed native subalgebras;',ordered_entries,'ordered-translation entries')
