package org.deri.iris.rules.compiler;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.StringUtils;
import org.deri.iris.api.basics.IPredicate;

public abstract class BodyRuleElement extends RuleElement {

  public abstract View getView();

  public abstract IPredicate getPredicate();

  @Override
  public String toString() {
    return StringUtils.join(getPredicate().toString(), IOUtils.LINE_SEPARATOR, getView().toString());
  }
}
