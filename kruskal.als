open util/integer
open util/ordering[State]
open lib/graph
open MST
open lib/properties

sig State {
	g : one UGraph,
	parentSet : Vertex -> Vertex,
	remainingEdges : set Edge,
	edgesInMST : set Edge
	//idk some other things like clouds?
}

fact {
	all s : State |
		some s.g.edges
}

fun minEdge(es : set Edge) : Edge {
	{e : es | no e2 : es | lt[e2.weight, e.weight]}
}

pred isAddable(e : Edge, s : State) {
	no e.v1.^(s.parentSet) & e.v2.^(s.parentSet)
}

fact initialState {
	connected[first.g.edges, first.g.vertices]
	all v1, v2 : Vertex |
		v1->v2 in first.parentSet iff (v1 = v2) and (v1 in first.g.vertices)
	first.remainingEdges = first.g.edges
	no first.edgesInMST
}

fact endState {
	no last.remainingEdges
	isMST[last.edgesInMST, last.g]
}

abstract sig Event {
	pre, post : State
}

sig addEdge extends Event { }
{
	post.g = pre.g
	let minE = minEdge[pre.remainingEdges] {
		isAddable[minE, pre] implies {
			post.edgesInMST = pre.edgesInMST + minE
			post.parentSet = pre.parentSet - (minE.v1 -> minE.v1) + (minE.v1 -> minE.v2)

		}
		post.remainingEdges = pre.remainingEdges - minE
		post.parentSet = pre.parentSet
	}
}

fact transitions {
	all s: State - last |
		let s' = s.next |
			one e: Event | e.pre = s and e.post = s'
}

run { }
