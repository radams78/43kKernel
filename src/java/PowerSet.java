import java.util.*;

public class PowerSet<T> extends ArrayList<TreeSet<T> > {
	
	// autoadd
	private static final long serialVersionUID = 2968669418764153495L;

	public PowerSet(TreeSet<T> S) {
		super();
		
		if(S.isEmpty()) {
			add(new TreeSet<T> ());
			return;
		}
		
		TreeSet<T> SS = new TreeSet<T> (S);
		SS.remove(S.first());
		
		PowerSet<T> allSmall = new PowerSet<T>(SS);
		addAll(allSmall);

		PowerSet<T> allBig = new PowerSet<T>(SS);
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
		PowerSet<Integer> Z = new PowerSet<Integer>(X);
		System.out.println(Z);
	}
}

