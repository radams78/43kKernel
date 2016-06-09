
import java.io.File;
import java.util.*;

public class DistinctSignatureEnumerator {

	BoundaryGarden myGarden;
	ArrayList<BasicRegionGenerator> basicRegionsByBoundary;
	
	ArrayList<ArrayList<Region> > allSignatureMinimalRegionsByBoundary;
	boolean computedAllSignatureMinimal;
	
	public ArrayList<Region> allSignatureMinimalRegionsOfBoundaryType(int boundaryID) {
		if(!computedAllSignatureMinimal) setAllSignatureMinimalRegions();
		return new ArrayList<Region> (allSignatureMinimalRegionsByBoundary.get(boundaryID));
	}
	
	public ArrayList<Region> allSignatureMinimalRegionsOfBoundaryType(String name) {
		return allSignatureMinimalRegionsOfBoundaryType(myGarden.getIdOfBoundaryWithName(name));
	}
	
	DistinctSignatureEnumerator(String boundaryFile) throws Exception {
		System.out.print("Reading input ...");
		BoundaryListReader BLR = new BoundaryListReader(new Scanner(new File("boundaries.txt")));
		Pair<ArrayList<Boundary>, ArrayList<String> > BL = BLR.readBoundaries();
		BLR.close();
		System.out.println("done.");
	
		System.out.print("Populating Boundary Garden ... ");
		myGarden = new BoundaryGarden(BL.first, BL.second);
		System.out.println("done.");
	
		System.out.print("Generating All Basic Regions ... ");
		basicRegionsByBoundary = new ArrayList<BasicRegionGenerator> (); 
		for(int i = 0; i < myGarden.n; ++i) {basicRegionsByBoundary.add(new BasicRegionGenerator(myGarden, i));}
		System.out.println("done.");
	
		computedAllSignatureMinimal = false;
	}
	
	private void setAllSignatureMinimalRegions() {
		allSignatureMinimalRegionsByBoundary = new ArrayList<ArrayList<Region> > ();
		for(int i = 0; i < myGarden.n; ++i) allSignatureMinimalRegionsByBoundary.add(new ArrayList<Region> ());
		
		ArrayList<HashSet<BitSet> > discoveredSignatures = new ArrayList<HashSet<BitSet> > ();
		for(int i = 0 ; i < myGarden.n; ++i) discoveredSignatures.add(new HashSet<BitSet> ());
		
		ArrayList<Queue<Region> > regionQueue = new ArrayList<Queue<Region> > ();
		for(int i = 0; i < 12; ++i) {regionQueue.add(new LinkedList<Region> ());}

		// make queue
		int totalQueueSize = 0;
		for(int i = 0; i < myGarden.n; ++i) {
			for(Region r : basicRegionsByBoundary.get(i).getAllBasicRegions()) {
				regionQueue.get(r.size).add(r);
				totalQueueSize++;
		}}
		
		int regSize = 0;
		int largestNonEmpty = -1;
		while(totalQueueSize > 0) {
			
			if(regionQueue.size() <= regSize + 12) {
				for(int i = 0; i < 12; ++i) {regionQueue.add(new LinkedList<Region> ());}
				System.out.println("Enlarged queue to size " + regionQueue.size() + " regions.");
			}
			
			System.out.print("Regions of size " + regSize + " ... ");
			int popped = 0;
			int newUndiscovered = 0;

			int queueSizeDecrement = (regionQueue.get(regSize).size() / 10) + 1;
			
			while(!regionQueue.get(regSize).isEmpty()) {
				popped++;
				
				if(regionQueue.get(regSize).size() % queueSizeDecrement == 0) System.out.print(".");	
				
				Region nextRegion = regionQueue.get(regSize).poll();
				totalQueueSize--;
				BitSet transcript = nextRegion.getSignature().store();
				int ID = nextRegion.boundaryID;
				
				if(!discoveredSignatures.get(ID).contains(transcript)) {
					allSignatureMinimalRegionsByBoundary.get(ID).add(nextRegion);
					discoveredSignatures.get(ID).add(transcript);	
					largestNonEmpty = largestNonEmpty > regSize ? largestNonEmpty : regSize;
					newUndiscovered++;
					
					// Add all extensions to queue
					for(int bottomBoundaryID : myGarden.getGluesOnto(ID)) {
						for(BasicRegion bottomRegion : basicRegionsByBoundary.get(bottomBoundaryID).getAllBasicRegions()) {
							Region extension = new CompositeRegion(myGarden, nextRegion, bottomRegion);
							regionQueue.get(extension.size).add(extension);
							totalQueueSize++;
						}
					}
					
				}
			}
			System.out.println(" done. Total popped " + popped + " discovered: " + newUndiscovered);
			regSize++;
		}
		System.out.println("Max number of vertices in a signature-minimal region: " + largestNonEmpty);
		computedAllSignatureMinimal = true;
	}
	
	
	
	
	
	public static void main(String[] args) throws Exception {
		DistinctSignatureEnumerator DSE = new DistinctSignatureEnumerator("boundaries.txt");
		ArrayList<Region> allType22 = DSE.allSignatureMinimalRegionsOfBoundaryType("T22");
		
		System.out.println(allType22.size());
		
		// if(newUndiscovered % 1000 == 0) System.out.print("!");	
		/*
		if(regSize == 14) {
			
			SignatureTranscript regionInfo = nextRegion.getSignatureTranscript();
			System.out.println(regionInfo.sig);
			
			regionInfo.dumpToFile("rs" + regSize + "nr" + newUndiscovered + ".txt", true);

			SignatureTranscript newRegionInfo = SignatureTranscript.readFromFile("rs" + regSize + "nr" + newUndiscovered + ".txt", true);
			System.out.println(newRegionInfo.sig);
			
			if(regionInfo.sig.equals(newRegionInfo.sig)) {
				System.out.println("hurra");
			} else {
				System.out.println("uffda");
			}
			
		}
		
		if(regSize == 14) {
			System.out.println("\n" + nextRegion.toString());
		}

		*/
	
	
	
	}
	
	public static void printBasicRegions(BoundaryGarden myGarden, ArrayList<BasicRegionGenerator> basicRegionsByBoundary) {
		for(int i = 0; i < myGarden.n; ++i) {
			System.out.println(basicRegionsByBoundary.get(i).getAllBasicRegions());
			System.out.println();
		}		
	}
	
}
