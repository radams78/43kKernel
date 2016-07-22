import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

public class PathOperator {
	
	public static Set<Vertex> pathNeighbors(ArrayList<Vertex> path, Set<Vertex> S) {
		Set<Vertex> ans = new TreeSet<Vertex> ();
		for(int p = 0; p < path.size(); ++p) {
			for(int pp = p-1; pp <= p+1; ++pp) {
					if(pp < 0 || pp >= path.size()) continue;
					if(S.contains(path.get(pp))) ans.add(path.get(p));
			}
		}
		return ans;
	}
	 
	public static List<Pair<Vertex, Vertex> > pathEdges (ArrayList<Vertex> path) {
		ArrayList<Pair<Vertex, Vertex> > ans = new ArrayList<Pair<Vertex, Vertex> > ();
		for(int i = 0; i + 1 < path.size(); ++i) {ans.add(new Pair<Vertex, Vertex> (path.get(i), path.get(i+1)));}
		return ans;
	}
	
}
