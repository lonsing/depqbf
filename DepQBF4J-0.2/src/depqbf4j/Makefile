#JAVA_HOME=/usr/lib/jvm/java-6-sun-1.6.0.26
JAVAC=/usr/bin/javac
JAVAH=/usr/bin/javah

.PHONY: all clean

all: DepQBF4J.class Example_basic_api_example.class Example_basic_api_example2.class Example_basic_api_example3.class Example_basic_manual_selectors.class Example_basic_clause_groups_api_example.class

DepQBF4J.class: DepQBF4J.java
	$(JAVAC) DepQBF4J.java

Example_basic_api_example.class: Example_basic_api_example.java DepQBF4J.class
	$(JAVAC) -classpath .. Example_basic_api_example.java

Example_basic_clause_groups_api_example.class: Example_basic_clause_groups_api_example.java DepQBF4J.class
	$(JAVAC) -classpath .. Example_basic_clause_groups_api_example.java

Example_basic_api_example2.class: Example_basic_api_example2.java DepQBF4J.class
	$(JAVAC) -classpath .. Example_basic_api_example2.java

Example_basic_api_example3.class: Example_basic_api_example3.java DepQBF4J.class
	$(JAVAC) -classpath .. Example_basic_api_example3.java

Example_basic_manual_selectors.class: Example_basic_manual_selectors.java DepQBF4J.class
	$(JAVAC) -classpath .. Example_basic_manual_selectors.java

clean:
	rm -f *.class
