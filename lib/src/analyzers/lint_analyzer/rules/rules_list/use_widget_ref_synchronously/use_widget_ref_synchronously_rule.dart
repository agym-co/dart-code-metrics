import 'package:analyzer/dart/ast/ast.dart';
import 'package:analyzer/dart/ast/token.dart';
import 'package:analyzer/dart/ast/visitor.dart';
import 'package:analyzer/dart/element/element.dart';
import 'package:analyzer/dart/element/nullability_suffix.dart';
import 'package:analyzer/dart/element/type.dart';

import '../../../../../utils/flutter_types_utils.dart';
import '../../../../../utils/node_utils.dart';
import '../../../lint_utils.dart';
import '../../../models/internal_resolved_unit_result.dart';
import '../../../models/issue.dart';
import '../../../models/severity.dart';
import '../../models/flutter_rule.dart';
import '../../rule_utils.dart';
import '../use_setstate_synchronously/fact.dart';

part 'helpers.dart';
part 'visitor.dart';

class UseWidgetRefSynchronouslyRule extends FlutterRule {
  static const ruleId = 'use-widgetref-synchronously';

  UseWidgetRefSynchronouslyRule([Map<String, Object> options = const {}])
      : super(
          id: ruleId,
          severity: readSeverity(options, Severity.warning),
          excludes: readExcludes(options),
          includes: readIncludes(options),
        );

  @override
  Iterable<Issue> check(InternalResolvedUnitResult source) {
    final visitor = _Visitor();
    source.unit.accept(visitor);

    return visitor.nodes
        .map((node) => createIssue(
              rule: this,
              location: nodeLocation(node: node, source: source),
              message: 'Avoid using WidgetRef past an await point without '
                  'checking if the widget is mounted.',
            ))
        .toList(growable: false);
  }
}
