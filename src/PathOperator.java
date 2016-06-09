import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

public class PathOperator {
	
	public static Set<Integer> pathNeighbors(ArrayList<Integer> path, Set<Integer> S) {
		Set<Integer> ans = new TreeSet<Integer> ();
		for(int p = 0; p < path.size(); ++p) {
			for(int pp = p-1; pp <= p+1; ++pp) {
					if(pp < 0 || pp >= path.size()) continue;
					if(S.contains(path.get(pp))) ans.add(path.get(p));
			}
		}
		return ans;
	}
	 
	public static List<Pair<Integer, Integer> > pathEdges (ArrayList<Integer> path) {
		ArrayList<Pair<Integer, Integer> > ans = new ArrayList<Pair<Integer, Integer> > ();
		for(int i = 0; i + 1 < path.size(); ++i) {ans.add(new Pair<Integer, Integer> (path.get(i), path.get(i+1)));}
		return ans;
	}
	
}
