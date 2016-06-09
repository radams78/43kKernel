import java.util.*;

public class PowerSet extends ArrayList<TreeSet<Integer> > {
	
	// autoadd
	private static final long serialVersionUID = 2968669418764153495L;

	public PowerSet(TreeSet<Integer> S) {
		super();
		
		if(S.isEmpty()) {
			add(new TreeSet<Integer> ());
			return;
		}
		
		TreeSet<Integer> SS = new TreeSet<Integer> (S);
		SS.remove(S.first());
		
		PowerSet allSmall = new PowerSet(SS);
		addAll(allSmall);

		PowerSet allBig = new PowerSet(SS);
		for(int i = 0; i < allBig.size(); ++i) {allBig.get(i).add(S.first());}
		addAll(allBig);
	}
	
	// For testing purposes only
	public static void main(String[] args) {
		TreeSet<Integer> X = new TreeSet<Integer> ();
		X.add(1);
		X.add(2);
		X.add(3);
		X.add(5);
		PowerSet Z = new PowerSet(X);
		System.out.println(Z);
	}
}

