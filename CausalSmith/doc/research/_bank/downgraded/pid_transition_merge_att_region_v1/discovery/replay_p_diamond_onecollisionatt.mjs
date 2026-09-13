#!/usr/bin/env node
// Deterministic exact-rational generator and checker for
// art:p-diamond-onecollisionatt-v1. No floating-point arithmetic is used.

import { readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const artifactPath = join(here, "p_diamond_onecollisionatt.json");
const abs = x => x < 0n ? -x : x;
const gcd = (a,b) => { a=abs(a); b=abs(b); while(b!==0n) [a,b]=[b,a%b]; return a; };
class Q {
  constructor(n,d=1n) { n=BigInt(n); d=BigInt(d); if(d===0n) throw Error("zero denominator"); if(d<0n){n=-n;d=-d;} const g=gcd(n,d); this.n=n/g; this.d=d/g; }
  add(x){x=q(x);return new Q(this.n*x.d+x.n*this.d,this.d*x.d)}
  sub(x){x=q(x);return new Q(this.n*x.d-x.n*this.d,this.d*x.d)}
  mul(x){x=q(x);return new Q(this.n*x.n,this.d*x.d)}
  div(x){x=q(x);return new Q(this.n*x.d,this.d*x.n)}
  neg(){return new Q(-this.n,this.d)}
  eq(x){x=q(x);return this.n===x.n&&this.d===x.d}
  sign(){return this.n===0n?"zero":this.n>0n?"positive":"negative"}
}
const q=x=>x instanceof Q?x:typeof x==="string"?(()=>{const [n,d="1"]=x.split("/");return new Q(n,d)})():new Q(x);
const ZERO=q(0), ONE=q(1), eta=q("1/10"), U=q("9/10");
const sum=xs=>xs.reduce((a,b)=>a.add(b),ZERO);
const B=(p,x)=>x===1?p:ONE.sub(p);
const rat=x=>({numerator:Number(x.n),denominator:Number(x.d)});
const ratMap=o=>Object.fromEntries(Object.entries(o).map(([k,v])=>[k,rat(v)]));
const assert=(ok,msg)=>{if(!ok)throw Error(msg)};

const basePsi=()=>({
  pi:q("1/2"),
  e:{"1":q("3/5"),"2":q("2/5")},
  u:{"1,0":q("3/10"),"2,0":q("7/10"),"1,1":q("2/5"),"2,1":q("3/5")},
  a:{"1,0":q("3/10"),"1,1":q("4/5"),"2,0":q("3/10"),"2,1":q("4/5")},
  b3:{"1,0":q("1/5"),"1,1":q("3/5"),"2,0":q("3/5"),"2,1":q("3/10")},
  b4:{"1,0":q("1/2"),"1,1":q("7/10"),"2,0":q("1/2"),"2,1":q("2/5")},
  c3:{"1,0":q("3/10"),"1,1":q("7/10"),"2,0":q("3/5"),"2,1":q("1/5")},
  c4:{"1,0":q("1/5"),"1,1":q("7/10"),"2,0":q("4/5"),"2,1":q("3/10")}
});
const crossedPsi=()=>{
  const p=basePsi(); p.pi=q("3/5"); p.e={"1":q("1/2"),"2":q("1/2")};
  for(const f of ["u","b3","b4"]){const old={...p[f]};for(const rest of f==="u"?["0"]:["0","1"]){p[f]["1,"+rest]=old["2,"+rest];p[f]["2,"+rest]=old["1,"+rest];}}
  return p;
};
const swapPsi=p=>{
  const r={pi:ONE.sub(p.pi),e:{},u:{},a:{},b3:{},b4:{},c3:{},c4:{}};
  for(const f of ["e","u","a","b3","b4","c3","c4"])for(const [key,value] of Object.entries(p[f])){
    const [z,...rest]=key.split(",");r[f][[z==="1"?"2":"1",...rest].join(",")]=value;
  }
  return r;
};
const psiVariants={psi_diamond:basePsi(),psi_diamond_sw:crossedPsi()};
psiVariants.simswap_psi_diamond=swapPsi(psiVariants.psi_diamond);
psiVariants.simswap_psi_diamond_sw=swapPsi(psiVariants.psi_diamond_sw);
const piZ=(p,z)=>z===1?p.pi:ONE.sub(p.pi);
const fullPath=p=>{
  const out={};
  for(let i=0;i<2;i++)for(let j=0;j<2;j++)for(let k=0;k<2;k++)for(let l=0;l<2;l++)for(let d=0;d<2;d++){
    const key=""+i+j+k+l+d;
    out[key]=sum([1,2].map(z=>piZ(p,z).mul(B(p.e[""+z],d)).mul(B(p.u[z+","+d],i)).mul(B(p.a[z+","+i],j))
      .mul(B(p[d?"c3":"b3"][z+","+j],k)).mul(B(p[d?"c4":"b4"][z+","+k],l))));
  }
  return out;
};
const P=fullPath(psiVariants.psi_diamond);
for(const [name,p] of Object.entries(psiVariants)){const f=fullPath(p);for(const key of Object.keys(P))assert(f[key].eq(P[key]),name+" F mismatch "+key)}
assert(sum(Object.values(P)).eq(ONE),"PMF sum");
const pd={
  0:sum(Object.entries(P).filter(([k])=>k[4]==="0").map(([,v])=>v)),
  1:sum(Object.entries(P).filter(([k])=>k[4]==="1").map(([,v])=>v))
};
assert(pd[0].eq(q("1/2"))&&pd[1].eq(q("1/2")),"arm masses");
const H={},N={};
for(let d=0;d<2;d++)for(let i=0;i<2;i++)for(let j=0;j<2;j++)for(let k=0;k<2;k++){
  const key=""+d+i+j+k;
  H[key]=sum([0,1].map(l=>P[""+i+j+k+l+d])).div(pd[d]);
  N[key]=P[""+i+j+k+1+d].div(pd[d]);
}
const chi={};
for(let d=0;d<2;d++)for(let k=0;k<2;k++)for(const ij of ["01","10","11"]){
  const [i,j]=[...ij].map(Number);
  chi[""+d+k+ij]=N[""+d+i+j+k].mul(H[""+d+0+0+k]).sub(N[""+d+0+0+k].mul(H[""+d+i+j+k]));
}
for(const ij of ["01","10","11"])assert(chi["00"+ij].eq(ZERO),"k0 collision "+ij);
assert(chi["0101"].eq(q("11907/12500000")),"wrong-k0 minor");

const yLeaves={
  y_AA:["1/5","4/5","7/10","3/10","7/10","2/5","98/625","21/625","12/625","24/625"].map(q),
  y_AB:["1/5","4/5","7/10","3/10","2/5","7/10","63/1250","189/5000","21/625","147/625"].map(q),
  y_BA:["4/5","1/5","3/10","7/10","7/10","2/5","98/625","21/625","12/625","24/625"].map(q),
  y_BB:["4/5","1/5","3/10","7/10","2/5","7/10","63/1250","189/5000","21/625","147/625"].map(q)
};
const leafSigns={y_AA:"+-+",y_AB:"--+",y_BA:"++-",y_BB:"-+-"};
const Rkey=(z,d,i,j,k)=>""+z+d+i+j+k;
const splitLeaf=(y,k0=0)=>{
  const v={"110":y[0],"210":y[1],"111":y[2],"211":y[3]};
  const vbar=N["0"+0+0+k0].div(H["0"+0+0+k0]);v["10"+k0]=vbar;v["20"+k0]=vbar;v["10"+(1-k0)]=y[4];v["20"+(1-k0)]=y[5];
  const R={};let ix=6;
  for(let i=0;i<2;i++)for(let j=0;j<2;j++){R[Rkey(1,0,i,j,k0)]=y[ix++];R[Rkey(2,0,i,j,k0)]=H["0"+i+j+k0].sub(R[Rkey(1,0,i,j,k0)])}
  for(let d=0;d<2;d++)for(let k=0;k<2;k++){if(d===0&&k===k0)continue;for(let i=0;i<2;i++)for(let j=0;j<2;j++){
    const r1=N[""+d+i+j+k].sub(v["2"+d+k].mul(H[""+d+i+j+k])).div(v["1"+d+k].sub(v["2"+d+k]));
    R[Rkey(1,d,i,j,k)]=r1;R[Rkey(2,d,i,j,k)]=H[""+d+i+j+k].sub(r1);
  }}
  return {v,R};
};
const localFromSplit=({v,R})=>{
  const T={},S={},w={},u={},a={},k3={};
  for(let z=1;z<=2;z++)for(let d=0;d<2;d++){
    for(let i=0;i<2;i++)for(let j=0;j<2;j++)T[""+z+d+i+j]=sum([0,1].map(k=>R[Rkey(z,d,i,j,k)]));
    for(let i=0;i<2;i++)S[""+z+d+i]=sum([0,1].map(j=>T[""+z+d+i+j]));
    w[""+z+d]=S[""+z+d+0].add(S[""+z+d+1]);u[""+z+d]=S[""+z+d+1].div(w[""+z+d]);
    for(let i=0;i<2;i++)a[""+z+d+i]=T[""+z+d+i+1].div(S[""+z+d+i]);
    for(let j=0;j<2;j++)k3[""+z+d+j]=R[Rkey(z,d,0,j,1)].div(T[""+z+d+0+j]);
  }
  return {T,S,w,u,a,k3};
};
const reconstruct=(split,sigma)=>{
  const L=localFromSplit(split),ctl=z=>sigma==="id"?z:3-z,out={pi:ZERO,e:{},u:{},a:{},b3:{},b4:{},c3:{},c4:{}},pis={};
  for(let z=1;z<=2;z++){
    pis[z]=pd[0].mul(L.w[""+ctl(z)+0]).add(pd[1].mul(L.w[""+z+1]));out.e[""+z]=pd[1].mul(L.w[""+z+1]).div(pis[z]);
    out.u[z+",0"]=L.u[""+ctl(z)+0];out.u[z+",1"]=L.u[""+z+1];
    for(let i=0;i<2;i++)out.a[z+","+i]=L.a[""+z+1+i];
    for(let j=0;j<2;j++){out.b3[z+","+j]=L.k3[""+ctl(z)+0+j];out.c3[z+","+j]=L.k3[""+z+1+j]}
    for(let k=0;k<2;k++){out.b4[z+","+k]=split.v[""+ctl(z)+0+k];out.c4[z+","+k]=split.v[""+z+1+k]}
  }
  out.pi=pis[1];return {psi:out,local:L};
};
const samePsi=(a,b)=>a.pi.eq(b.pi)&&["e","u","a","b3","b4","c3","c4"].every(f=>Object.keys(a[f]).every(k=>a[f][k].eq(b[f][k])));
const serializePsi=p=>({pi:rat(p.pi),e:ratMap(p.e),u:ratMap(p.u),a:ratMap(p.a),b3:ratMap(p.b3),b4:ratMap(p.b4),c3:ratMap(p.c3),c4:ratMap(p.c4)});
const primitiveList=p=>{const xs=[["pi",p.pi]];for(const f of ["e","u","a","b3","b4","c3","c4"])for(const k of Object.keys(p[f]).sort())xs.push([f+"."+k.replace(",", "."),p[f][k]]);return xs};
const atom=(id,expression,required_relation,value,cleared=null)=>({id,expression,required_relation,value:rat(value),sign:value.sign(),...(cleared===null?{}:{cleared_value:rat(cleared),cleared_sign:cleared.sign()})});
const evalG=(leafName,sigma)=>{
  const y=yLeaves[leafName],split=splitLeaf(y),{psi,local:L}=reconstruct(split,sigma),atoms=[];
  for(let z=1;z<=2;z++)for(let d=0;d<2;d++)for(let j=0;j<2;j++){
    const rho=split.R[Rkey(z,d,0,j,0)].mul(split.R[Rkey(z,d,1,j,1)]).sub(split.R[Rkey(z,d,0,j,1)].mul(split.R[Rkey(z,d,1,j,0)]));
    atoms.push(atom("rho.z"+z+".d"+d+".j"+j,"R_"+z+d+"(0,"+j+",0)R_"+z+d+"(1,"+j+",1)-R_"+z+d+"(0,"+j+",1)R_"+z+d+"(1,"+j+",0)","=0",rho));
  }
  const ctl=z=>sigma==="id"?z:3-z;
  for(let z=1;z<=2;z++)for(let i=0;i<2;i++){
    const gamma=L.T[""+ctl(z)+0+i+1].mul(L.S[""+z+1+i]).sub(L.T[""+z+1+i+1].mul(L.S[""+ctl(z)+0+i]));
    atoms.push(atom("gamma."+sigma+".z"+z+".i"+i,"T_"+ctl(z)+"0("+i+",1)S_"+z+"1("+i+")-T_"+z+"1("+i+",1)S_"+ctl(z)+"0("+i+")","=0",gamma));
  }
  const signs=leafSigns[leafName],orient=[
    ["orientation.control.k1","s_01(v_101-v_201)",signs[0],split.v["101"].sub(split.v["201"])],
    ["orientation.treated.k0","s_10(v_110-v_210)",signs[1],split.v["110"].sub(split.v["210"])],
    ["orientation.treated.k1","s_11(v_111-v_211)",signs[2],split.v["111"].sub(split.v["211"])]
  ];
  for(const [id,expr,s,val] of orient)atoms.push(atom(id,expr,">0",s==="+"?val:val.neg()));
  const eta5=q("1/100000");
  for(const key of Object.keys(split.R).sort()){const r=split.R[key],cl=new Q(100000n*r.n-r.d);atoms.push(atom("mass.R."+key,"R_"+key+"-eta^5",">=0",r.sub(eta5),cl))}
  for(const [name,val] of primitiveList(psi)){
    const lo=new Q(10n*val.n-val.d),hi=new Q(9n*val.d-10n*val.n);
    atoms.push(atom("box.lower."+name,"10N_"+name+"-D_"+name,">=0",val.sub(eta),lo));
    atoms.push(atom("box.upper."+name,"9D_"+name+"-10N_"+name,">=0",U.sub(val),hi));
  }
  for(const a of atoms)assert(a.required_relation==="=0"?a.sign==="zero":a.required_relation===">0"?a.sign==="positive":a.sign!=="negative",leafName+"/"+sigma+" atom "+a.id);
  return {split,psi,atoms};
};
const att=p=>{
  const O={};
  for(const t of [3,4]){const pos=t===3?2:3;O[t]=sum(Object.entries(P).filter(([key])=>key[4]==="1"&&key[pos]==="1").map(([,v])=>v)).div(pd[1])}
  const wz={},m3={},m4={};
  for(let z=1;z<=2;z++){wz[z]=piZ(p,z).mul(p.e[""+z]).div(pd[1]);const m2=ONE.sub(p.u[z+",1"]).mul(p.a[z+",0"]).add(p.u[z+",1"].mul(p.a[z+",1"]));m3[z]=ONE.sub(m2).mul(p.b3[z+",0"]).add(m2.mul(p.b3[z+",1"]));m4[z]=ONE.sub(m3[z]).mul(p.b4[z+",0"]).add(m3[z].mul(p.b4[z+",1"]))}
  return {q3:O[3].sub(sum([1,2].map(z=>wz[z].mul(m3[z])))),q4:O[4].sub(sum([1,2].map(z=>wz[z].mul(m4[z]))))};
};
const reconstructedName={
  "y_AA,id":"psi_diamond","y_AA,sw":"psi_diamond_sw","y_AB,id":"psi_diamond_sw","y_AB,sw":"psi_diamond",
  "y_BA,id":"simswap_psi_diamond_sw","y_BA,sw":"simswap_psi_diamond","y_BB,id":"simswap_psi_diamond","y_BB,sw":"simswap_psi_diamond_sw"
};
const acceptedSigns=new Set(Object.values(leafSigns)),leafBySigns=Object.fromEntries(Object.entries(leafSigns).map(([k,v])=>[v,k]));
const signsList=[];for(const a of ["+","-"])for(const b of ["+","-"])for(const c of ["+","-"])signsList.push(a+b+c);
const label=(k0,s,sigma)=>"k"+k0+":s("+[...s].join(",")+"):sigma-"+sigma;
const accepted=[];
for(const s of ["+-+","--+","++-","-+-"])for(const sigma of ["id","sw"]){
  const leaf=leafBySigns[s],ev=evalG(leaf,sigma),name=reconstructedName[leaf+","+sigma];assert(samePsi(ev.psi,psiVariants[name]),leaf+"/"+sigma+" reconstruction");
  const f=fullPath(ev.psi),diffs={};for(const key of Object.keys(P))diffs[key]=f[key].sub(P[key]);assert(Object.values(diffs).every(x=>x.eq(ZERO)),"F check");
  const tau=att(ev.psi);
  accepted.push({label:label(0,s,sigma),k0:0,orientation:{order:["s_0,1-k0","s_1,0","s_1,1"],signs:[...s]},alignment:sigma,equality_leaf:leaf,y:yLeaves[leaf].map(rat),reconstructed_member:name,reconstructed_psi:serializePsi(ev.psi),full_path_check:{equation:"F(reconstructed_psi)=P_diamond",cellwise_differences:ratMap(diffs),all_zero:true},att:{q3:rat(tau.q3),q4:rat(tau.q4)},g_atom_evaluations:ev.atoms});
}
assert(accepted.length===8,"accepted count");
const firstViolation=(required,actual)=>{
  const ids=["orientation.control.k1","orientation.treated.k0","orientation.treated.k1"],exprs=["s_01(v_101-v_201)","s_10(v_110-v_210)","s_11(v_111-v_211)"],split=splitLeaf(yLeaves[leafBySigns[actual]]),vals=[split.v["101"].sub(split.v["201"]),split.v["110"].sub(split.v["210"]),split.v["111"].sub(split.v["211"])];
  for(let i=0;i<3;i++)if(required[i]!==actual[i])return atom(ids[i],exprs[i],">0",required[i]==="+"?vals[i]:vals[i].neg());
  throw Error("no violation");
};
const rationalSample=name=>({kind:"rational-point",coordinate_order:["v110","v210","v111","v211","v10,1-k0","v20,1-k0","r00","r01","r10","r11"],coordinates:yLeaves[name].map(rat)});
const rejected=[];
for(let k0=0;k0<2;k0++)for(const s of signsList)for(const sigma of ["id","sw"]){
  if(k0===0&&acceptedSigns.has(s))continue;
  if(k0===1)rejected.push({label:label(k0,s,sigma),k0,s:[...s],alignment:sigma,status:"rejected",certificate_type:"nonzero-required-collision-minor",certificate:atom("collision.control.k1.ij01","N_0(0,1,1)H_0(0,0,1)-N_0(0,0,1)H_0(0,1,1)","=0",chi["0101"])});
  else{
    const audits=Object.keys(yLeaves).map(name=>({equality_leaf:name,algebraic_sample:rationalSample(name),actual_orientation:[...leafSigns[name]],first_violated_original_atom:firstViolation(s,leafSigns[name])}));
    assert(audits.length===4&&audits.every(x=>x.first_violated_original_atom.sign==="negative"),"audit "+s+"/"+sigma);
    rejected.push({label:label(k0,s,sigma),k0,s:[...s],alignment:sigma,status:"rejected",certificate_type:"complete-specialized-lifting-leaf-audit",candidate_leaf_count:4,equality_leaf_exhaustion_ref:"benchmark_equality_leaf_exhaustion",candidate_leaves:audits});
  }
}
assert(rejected.length===24,"rejected count");
const repChecks=Object.fromEntries(Object.entries(psiVariants).map(([name,p])=>{
  const f=fullPath(p),diff=Object.fromEntries(Object.keys(P).map(k=>[k,f[k].sub(P[k])]));
  return [name,{psi:serializePsi(p),F_equals_P:Object.values(diff).every(x=>x.eq(ZERO)),cellwise_differences:ratMap(diff)}];
}));
const artifact={
  artifact_id:"art:p-diamond-onecollisionatt-v1",schema_version:1,
  claim_scope:"Fixed exact-rational execution record only; no certificate compression, tier lift, global collision atlas, near-collision result, or endpoint/Hausdorff asymptotics.",
  generator:"replay_p_diamond_onecollisionatt.mjs",arithmetic:"reduced rational BigInt; no floating point",
  input:{eta:rat(eta),theta:rat(ZERO),law:"P_diamond",cells:ratMap(P)},
  conventions:{cell_key:"ijkld with i,j,k,l,d in {0,1}",branch_sign_order:["s_0,1-k0","s_1,0","s_1,1"],thom_sequence:"(sgn p(alpha), sgn p'(alpha), ...)",clearing:"Only recorded positive denominators are cleared; box atoms use q=N_q/D_q with D_q>0 and eta=1/10."},
  exact_input_checks:{sum_P:rat(sum(Object.values(P))),p0:rat(pd[0]),p1:rat(pd[1]),representations:repChecks},
  instantiated_evaluation_map:{
    map:"(P,eta) -> (H,N,chi,G_k0,s,sigma)",H:ratMap(H),N:ratMap(N),chi:Object.fromEntries(Object.entries(chi).map(([k,v])=>[k,{value:rat(v),sign:v.sign()}])),
    canonical_polynomial_ids:{collision:"collision.control.k{k0}.ij{ij}",rank_one:"rho.z{z}.d{d}.j{j}",alignment:"gamma.{sigma}.z{z}.i{i}",orientation:["orientation.control.k1","orientation.treated.k0","orientation.treated.k1"],mass:"mass.R.{zdijk}",box:["box.lower.{primitive}","box.upper.{primitive}"]},
    benchmark_equality_leaf_exhaustion:{
      method:"Exact specialization of the recovery equations before orientation lifting.",
      treated_certificate:{invertible_terminal_determinants:[rat(q("3/5")),rat(q("2/5"))],invertible_prefix_determinants:[rat(q("21/3125")),rat(q("36/3125"))],eigenvalues:[rat(q("9/49")),rat(q(6))],eigenvalue_gap:rat(q("285/49")),two_labeled_terminal_solutions:[[rat(q("1/5")),rat(q("4/5")),rat(q("7/10")),rat(q("3/10"))],[rat(q("4/5")),rat(q("1/5")),rat(q("3/10")),rat(q("7/10"))]]},
      control_certificate:{observable_row_differences:[rat(q("-32/207")),rat(q("8/69"))],terminal_zero_row_determinants:[rat(q("128/1035")),rat(q("112/1035"))],component_root_polynomial:"(5v-2)(10v-7)",roots:[rat(q("2/5")),rat(q("7/10"))],two_labeled_solutions:[[rat(q("7/10")),rat(q("2/5"))],[rat(q("2/5")),rat(q("7/10"))]]},
      cross_product_statement:"The two exact labeled treated solutions and two exact labeled control solutions give exactly y_AA,y_AB,y_BA,y_BB; direct substitution evaluates all eight rho and four gamma equalities to zero for each alignment.",
      leaves:Object.fromEntries(Object.keys(yLeaves).map(name=>[name,rationalSample(name)]))
    }
  },
  branches:{enumerated_count:32,accepted_count:8,rejected_count:24,accepted,rejected},
  output:{
    joint_formula:"((250*q3-9=0) AND (2500*q4+33=0)) OR ((500*q3+1=0) AND (5000*q4-49=0))",
    marginal_q3:"(500*q3+1=0) OR (250*q3-9=0)",marginal_q4:"(2500*q4+33=0) OR (5000*q4-49=0)",
    endpoints:[
      {coordinate:"q3",value:rat(q("-1/500")),primitive_polynomial:"500*q3+1",isolating_interval:[rat(q("-1/400")),rat(q("-1/600"))],thom_signs:["zero","positive"]},
      {coordinate:"q3",value:rat(q("9/250")),primitive_polynomial:"250*q3-9",isolating_interval:[rat(q("1/30")),rat(q("1/25"))],thom_signs:["zero","positive"]},
      {coordinate:"q4",value:rat(q("-33/2500")),primitive_polynomial:"2500*q4+33",isolating_interval:[rat(q("-7/500")),rat(q("-13/1000"))],thom_signs:["zero","positive"]},
      {coordinate:"q4",value:rat(q("49/5000")),primitive_polynomial:"5000*q4-49",isolating_interval:[rat(q("9/1000")),rat(q("1/100"))],thom_signs:["zero","positive"]}
    ]
  },
  replay_assertions:{all_32_cells_literal:Object.keys(P).length===32,pmf_checks:true,representation_checks:true,accepted_atom_checks:true,rejected_leaf_audits_complete:true,normalized_output_checks:true}
};
const canonical=JSON.stringify(artifact,null,2)+"\n";
if(process.argv.includes("--write"))writeFileSync(artifactPath,canonical,"utf8");
else assert(readFileSync(artifactPath,"utf8")===canonical,"artifact differs from deterministic replay");
console.log(JSON.stringify({status:"verified",artifact:artifact.artifact_id,path:artifactPath,cells:32,accepted:8,rejected:24}));
