import java.io.*;

public class CoqObjectTest {
    static final String REQUIRE_IMPORT = "Require Import";

    public static <T extends CoqObject> void testObject(String dir, String output_file, String[] imports, T testObject, String name) throws FileNotFoundException {
	PrintWriter writer = new PrintWriter(dir + "/" + output_file);
	for (String imp : imports)
	    writer.println(REQUIRE_IMPORT + " " + imp + ".");
	writer.println();
	writer.println(testObject.definition(name));
	writer.close();
    }
}
