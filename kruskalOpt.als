open util/integer
open util/natural
open util/ordering[State]
open lib/graph
open MST
open lib/properties

sig State {
	// The graph we're operating on
	g : one UGraph,

	// Clouds
	parentSet : Vertex -> Vertex,

	// Ranks
	ranks : Vertex -> Natural,

	// Edges we haven't tried to add yet
	remainingEdges : set Edge,

	// The edges that we've already added to our MST
	edgesInMST : set Edge
}{
	some g.edges
}

fun minEdges(es : set Edge) : Edge {
	// This returns the set of the edges of the smallest weight if there are multiple
	{e : es | no e2 : es | lt[e2.weight, e.weight]}
}

pred isAddable(e : Edge, s : State) {
	// If they're in different trees, this edge is addable
	findParent[e.v1, s] != findParent[e.v2, s]
}

fact initialState {
	// Otherwise this will return a spanning forest instead of a spanning tree
	connected[first.g.edges, first.g.vertices]

	// All parent pointers start off pointing to themselves
	all v1, v2 : Vertex |
		v1 -> v2 in first.parentSet iff (v1 = v2) and (v1 in first.g.vertices)

	// Initial ranks are 0
	first.ranks = Vertex -> Zero

	first.remainingEdges = first.g.edges
	no first.edgesInMST
}

fact endState {
	no last.remainingEdges
}

abstract sig Event {
	pre, post : State
}

sig addEdge extends Event { }
{
	// These all must be operating on the same graph!
	post.g = pre.g

	// Go in order of edge weight
	let minEs = minEdges[pre.remainingEdges] {
		some minE : minEs | {
			isAddable[minE, pre] => {
				// Add it to the MST and update the parent pointers
				post.edgesInMST = pre.edgesInMST + minE
				// If r
				minE.v1.(pre.ranks) = minE.v2.(pre.ranks) =>{
					let p1 = findParent[minE.v1, pre] | let p2 = findParent[minE.v2, pre] |
							post.parentSet = pre.parentSet - (p1->p1) + (p1->p2)
					let curRank = minE.v2.(pre.ranks) | 
							post.ranks = pre.ranks - (minE.v2 -> curRank) + (minE.v2 -> inc[curRank])

				} else { lt[minE.v1.(pre.ranks), minE.v2.(pre.ranks)] => {
					let p1 = findParent[minE.v1, pre] | let p2 = findParent[minE.v2, pre] |
						post.parentSet = pre.parentSet - (p1->p1) + (p1->p2)
					post.ranks = pre.ranks
				
				} else {
					let p1 = findParent[minE.v2, pre] | let p2 = findParent[minE.v1, pre] |
						post.parentSet = pre.parentSet - (p1->p1) + (p1->p2)
					post.ranks = pre.ranks			
				}}
			} else {
				// The clouds/MST are still the same
				post.edgesInMST = pre.edgesInMST
				post.parentSet = pre.parentSet
				post.ranks = pre.ranks
			}
			post.remainingEdges = pre.remainingEdges - minE
		}
	}
}

fun smallerRanks(e : Edge, s : State) : Vertex {
	let vs = e.v1 + e.v2 |
		{v1 : vs | no v2 : vs | lt[v2.(s.ranks), v1.(s.ranks)]}
}

fun findParent(v : Vertex, s : State) : Vertex {
	{parent: v.^(s.parentSet) | parent -> parent in s.parentSet}
}

fact transitions {
	all s: State - last |
		let s' = s.next |
			one e: Event | e.pre = s and e.post = s'
}

fact {
	some disj e1, e2 : Edge | e1.weight = e2.weight
}

assert findsMST {
	isMST[last.edgesInMST, last.g]
}

check findsMST for 10 Int, 3 Natural, exactly 3 Edge, 1 Graph, 3 Vertex, 4 State, 3 Event
//check findsMST for 10 Int, 3 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event

run { } for 10 Int, 5 Natural, exactly 6 Edge, 1 Graph, 4 Vertex, 7 State, 6 Event
//run { } for 10 Int, 9 Natural, exactly 10 Edge, 1 Graph, 5 Vertex, 11 State, 10 Event
