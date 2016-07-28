import java.util.*;
import java.io.*;

public class SignatureTranscript {

	Boundary myBoundary;
	ArrayList<InputPair> inputs;
	ArrayList<Integer> sig; 
	
	SignatureTranscript(Boundary b, Signature s) {
		myBoundary = b;
		sig = s.getSignatureCopy();
		inputs = b.allValidInputs();
	}
	
	SignatureTranscript(Region r) {
		myBoundary = r.myBoundary;
		inputs = myBoundary.allValidInputs();
		sig = r.getSignature().getSignatureCopy();
	}

	public static ArrayList<SignatureTranscript> readListFromFile(String filename, boolean johanStyle) {
		return readListFromFile(filename, 1000000, johanStyle);
	}

	public static ArrayList<SignatureTranscript> readListFromFile(String filename, int maxRead, boolean johanStyle) {
		Scanner sc = new Scanner("dummy");
		try {
			sc = new Scanner(new File(filename));
		} catch(Exception e) {
			System.out.println("Shit went wrong when reading from file");
			System.out.println(e);
			System.exit(1);
		}
	
		ArrayList<SignatureTranscript> ans = new ArrayList<SignatureTranscript> ();
		int read = 0;
		while(sc.hasNext() && read < maxRead) {
			ans.add(readFromScanner(sc, johanStyle));
			read++;
			if(read % 1000 == 0) System.out.println(read/1000);
		}
		sc.close();
		return ans;
	}
	
	
	
	
	
	public static SignatureTranscript readFromFile(String filename, boolean johanStyle) {
		Scanner sc = new Scanner("dummy");
		try {
			sc = new Scanner(new File(filename));
		} catch(Exception e) {
			System.out.println("Shit went wrong when reading from file");
			System.out.println(e);
			System.exit(1);
		}

		return readFromScanner(sc, johanStyle);
	}

	
	// Reads a single signature transcript from a scanner.
	public static SignatureTranscript readFromScanner(Scanner sc, boolean johanStyle) {
		// Read boundary
		ArrayList<Vertex> topPath = new ArrayList<Vertex> ();
		ArrayList<Vertex> bottomPath = new ArrayList<Vertex> ();

		String name = sc.nextLine();
			
		int tps = sc.nextInt();
		while(tps-->0) topPath.add(new Vertex(sc.nextInt()));
		int bps = sc.nextInt();
		while(bps-->0) bottomPath.add(new Vertex(sc.nextInt()));
			
		Boundary inBoundary = new Boundary(topPath, bottomPath);
		Boundary boundary = inBoundary.canonicalBoundary();
		VertexRenamer canonizer = inBoundary.canonicalRenamer();
			
		ArrayList<InputPair> allInputs = boundary.allValidInputs();
				
		int numInputs = sc.nextInt();
		assert numInputs == allInputs.size() : "Wrong number of inputs";
			
		ArrayList<Integer> sig = new ArrayList<Integer> ();
		for(int i = 0; i < numInputs; ++i) sig.add(0);
			
		// Read the signature.
		while(numInputs-->0) {
			Set<Vertex> X = new TreeSet<Vertex> ();
			Set<Vertex> D = new TreeSet<Vertex> ();
				
			int xs = sc.nextInt();
			while(xs-->0) X.add(new Vertex(sc.nextInt()));
			X = canonizer.renamedSet(X);
				
			int ds = sc.nextInt();
			while(ds-->0) D.add(new Vertex(sc.nextInt()));
			D = canonizer.renamedSet(D);
				
			InputPair inp = new InputPair(X,D);
			if(johanStyle) inp = boundary.fromJohanStyle(inp);
				
			int inpPosition = allInputs.indexOf(inp);
			assert inpPosition != -1 : "Could not find input : " + inp + " for boundary: " + boundary 
					                   + " , \n originally: " + inBoundary;
				
			sig.set(inpPosition, sc.nextInt());
		}

		return new SignatureTranscript(boundary, new Signature(sig)); 
	}
	
	static <T> String intSetToString (Set<T> X) {
		StringBuffer ans = new StringBuffer();
		ans.append(X.size() + " ");
		for(T x : X) ans.append(x + " ");
		return ans.toString();
	}
	
		
	// Set to false for Daniel style, true for JohanStyle
	void dumpToFile(String filename, boolean johanStyle) {
			
		PrintWriter writer = null;
		try{
			
			writer = new PrintWriter(filename, "UTF-8");

		} catch(Exception e) {
			System.out.println("Shit went wrong when writing to file");
			System.out.println(e);
			System.exit(1);
		}

		writer.print(myBoundary.topPathLength() + 2 + " ");
		for(int i = 0; i < myBoundary.topPathLength() + 2; ++i) writer.print(myBoundary.topPathVertex(i) + " ");
		writer.println();
		
		writer.print(myBoundary.bottomPathLength() + 2 + " ");
		for(int i = 0; i < myBoundary.bottomPathLength() + 2; ++i) writer.print(myBoundary.bottomPathVertex(i) + " ");
		writer.println();
		
		writer.println(inputs.size());
		for(int i = 0; i < inputs.size(); ++i) {
			InputPair p = inputs.get(i);
			if(johanStyle) p = myBoundary.toJohanStyle(p);
			writer.println(intSetToString(p.first));
			writer.println(intSetToString(p.second));
			writer.println(sig.get(i));
		}
		writer.close();
	
	}
	
	public static void main(String[] args) {
		SignatureTranscript trans = SignatureTranscript.readFromFile("region1.txt", true);
		System.out.println(trans.sig);
	}

	public boolean equals(Object o) {
		if(!(o instanceof SignatureTranscript)) return false;
		SignatureTranscript s = (SignatureTranscript) o;
		return (myBoundary.equals(s.myBoundary)) && sig.equals(s.sig);
	}

	public String toString() {
		StringBuffer ans = new StringBuffer();
		for(int i = 0; i < inputs.size(); ++i) ans.append(inputs.get(i).toString() + " --> " + sig.get(i) + "\n");
		return ans.toString();
	}
	
	public void compareWith(SignatureTranscript t) {
		if(!(myBoundary.equals(t.myBoundary))) {
			System.out.println("Not equal boundaries");
			return;
		}
		
		for(int i = 0; i < inputs.size(); ++i) {
			if(sig.get(i) != t.sig.get(i)) {
				System.out.println(inputs.get(i) + "  this: " + sig.get(i) + "  other: " + t.sig.get(i));
			}
		}
		
		if(!equals(t)) System.out.print("not "); 
		System.out.println("equal transctipts");
	}
	

}
