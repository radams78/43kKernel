import java.util.*;

public class CompositeRegionDescriptor extends RegionDescriptor {

	public ArrayList<BasicRegionDescriptor> components;
	
	CompositeRegionDescriptor(RegionDescriptor topRegionDescr, BasicRegionDescriptor bottomRegionDescr) {
		components = new ArrayList<BasicRegionDescriptor> ();
		if(topRegionDescr instanceof BasicRegionDescriptor) {
			components.add((BasicRegionDescriptor) topRegionDescr); 
		} else if (topRegionDescr instanceof CompositeRegionDescriptor) {
			components.addAll(((CompositeRegionDescriptor) topRegionDescr).components);
		} else {
			assert false : "Descriptor Malfunction";
		}
		
		components.add(bottomRegionDescr);
	}
	
	public String toString() {
		StringBuffer ans = new StringBuffer();
		for(BasicRegionDescriptor b : components) ans.append(b.toString() + "\n");
		return ans.toString();
	}

}
