import csv, json, itertools, networkx as nx
from edges_v3 import EDGES
nombres={"E0":"Investigación general","E1":"Investigación especial","E2":"Interpretación","E3":"Historia","E4":"Dialéctica","E5":"Fundamentos","E6":"Doctrinas","E7":"Sistematización","E8":"Comunicaciones"}
tipos={"F":"cadena formal","R":"retorno formalizado","D":"entrada directa","H":"hipotetico"}
def G(tp,nodes=None):
    g=nx.DiGraph(); g.add_nodes_from(nodes or nombres)
    for a,b,t,*_ in EDGES:
        if t in tp: g.add_edge(a,b)
    return g
core=[f"E{i}" for i in range(1,9)]
gFR=G({"F","R"}); aut=gFR.subgraph(core).copy()
out={"n":{t:sum(e[2]==t for e in EDGES) for t in "FRDH"},"total":len(EDGES)}
out["autorizadas_E1_E8"]=aut.number_of_edges()
out["fuerte_E1_E8"]=nx.is_strongly_connected(aut)
crit=[];red=[]
for a,b in aut.edges():
    h=aut.copy(); h.remove_edge(a,b)
    (red if nx.is_strongly_connected(h) else crit).append(f"{a}→{b}")
out["criticas"]=crit; out["redundantes"]=red
# una cruzada basta / sin cruzadas
for rem in [[("E6","E3")],[("E5","E4")],[("E6","E3"),("E5","E4")]]:
    h=aut.copy(); h.remove_edges_from(rem); out["fuerte_sin_"+"_".join(f"{a}{b}" for a,b in rem)]=nx.is_strongly_connected(h)
gall=G({"F","R","D"}); 
out["F+R+D_fuerte_E1_E8"]=nx.is_strongly_connected(gall.subgraph(core))
out["todo_SCC"]=[sorted(c) for c in nx.strongly_connected_components(G({"F","R","D","H"}))]
out["FR_SCC"]=[sorted(c) for c in nx.strongly_connected_components(gFR)]
out["camino_E8_E1_mas_corto"]=nx.shortest_path(aut,"E8","E1")
out["camino_E0_E8"]=nx.shortest_path(gFR,"E0","E8")
out["ciclos_simples_FR"]=sum(1 for _ in nx.simple_cycles(aut))
bc=nx.betweenness_centrality(aut); out["intermediacion_FR"]={k:round(v,3) for k,v in sorted(bc.items(),key=lambda x:-x[1])}
gA=G({"F","R","D","H"})
out["entrada"]=dict(gA.in_degree()); out["salida"]=dict(gA.out_degree())
print(json.dumps(out,ensure_ascii=False,indent=1))
with open("aristas_E0_E8.csv","w",newline="",encoding="utf-8-sig") as f:
    w=csv.writer(f); w.writerow(["origen","destino","tipo","que_fluye","lean_o_estado","origen_del_vinculo"])
    for a,b,t,wh,ln,o,_ in EDGES: w.writerow([a,b,tipos[t],wh,ln.replace("`",""),o])
g=nx.DiGraph()
for k,v in nombres.items(): g.add_node(k,nombre=v,fase=("mediadora" if 1<=int(k[1])<=4 else "mediada" if int(k[1])>=5 else "previa"))
for a,b,t,wh,ln,o,_ in EDGES: g.add_edge(a,b,tipo=tipos[t],fundamento=wh,lean=ln.replace("`",""),origen=o)
nx.write_graphml(g,"grafo_E0_E8.graphml",encoding="utf-8")
