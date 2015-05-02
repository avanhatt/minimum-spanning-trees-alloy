open util/integer
open graph

pred complete (edges : set Edge, verts : set Vertex) {
	verts = Vertex.(edges.rels)
	all disj x, y : verts |
		some e : edges |
			(e.v1 = x and e.v2 = y) or (e.v2 = x and e.v1 = y)
}

pred directedAcyclic (g : DGraph) {
	all v : g.vertices |
		v->v not in ^(neighbors.g)
}

pred undirectedAcyclic (edges : set Edge, verts : set Vertex) {
	verts = Vertex.(edges.rels)
	all v1, v2: verts |
		let e = v1->v2 + v2->v1|
			e in edges.rels implies
				e not in ^(edges.rels - e)
}

pred connected (edges: set Edge, verts: set Vertex) {
	verts = Vertex.(edges.rels)
	all disj v1, v2 : verts |
		v1 in v2.^(edges.rels)
}

run complete

